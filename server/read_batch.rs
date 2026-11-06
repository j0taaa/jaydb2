//! Conservative read selection. This parses only enough canonical structure to
//! find a candidate handle. It grants no authentication or admission: the full
//! official Input.analyze still runs on the pinned snapshot for every request.
pub(super) fn candidate(body: &[u8]) -> Option<&str> {
    let mut bytes = body.strip_prefix(&[7, 1])?;
    if take(&mut bytes, 1)? != [6] || number(&mut bytes)? != 4 {
        return None;
    }
    if string(&mut bytes)? != "arguments" {
        return None;
    }
    skip(&mut bytes)?;
    if string(&mut bytes)? != "code" {
        return None;
    }
    string(&mut bytes)
}

fn take<'a>(bytes: &mut &'a [u8], n: usize) -> Option<&'a [u8]> {
    let (head, tail) = bytes.split_at_checked(n)?;
    *bytes = tail;
    Some(head)
}
fn number(bytes: &mut &[u8]) -> Option<u64> {
    Some(u64::from_be_bytes(take(bytes, 8)?.try_into().ok()?))
}
fn string<'a>(bytes: &mut &'a [u8]) -> Option<&'a str> {
    if take(bytes, 1)? != [4] {
        return None;
    }
    let n = usize::try_from(number(bytes)?).ok()?;
    std::str::from_utf8(take(bytes, n)?).ok()
}
fn skip(bytes: &mut &[u8]) -> Option<()> {
    // No recursion and no allocation, including for deeply nested arguments.
    let mut remaining = 1u64;
    while remaining != 0 {
        remaining -= 1;
        match take(bytes, 1)?[0] {
            0..=2 => {}
            3 => {
                take(bytes, 8)?;
            }
            4 => {
                let n = usize::try_from(number(bytes)?).ok()?;
                take(bytes, n)?;
            }
            5 => remaining = remaining.checked_add(number(bytes)?)?,
            6 => remaining = remaining.checked_add(number(bytes)?.checked_mul(2)?)?,
            _ => return None,
        }
        // Every pending value requires at least one remaining byte.
        if remaining > bytes.len() as u64 {
            return None;
        }
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn text(s: &str) -> Vec<u8> {
        let mut result = vec![4];
        result.extend_from_slice(&(s.len() as u64).to_be_bytes());
        result.extend_from_slice(s.as_bytes());
        result
    }
    #[test]
    fn candidates_require_the_execute_envelope_and_first_canonical_fields() {
        let mut body = vec![7, 1, 6];
        body.extend_from_slice(&4u64.to_be_bytes());
        body.extend(text("arguments"));
        body.push(0);
        body.extend(text("code"));
        body.extend(text("handle"));
        assert_eq!(candidate(&body), Some("handle"));
        for i in 0..body.len() {
            assert_eq!(candidate(&body[..i]), None);
        }
        for op in [0, 2, 3, 4] {
            body[1] = op;
            assert_eq!(candidate(&body), None);
        }
        body[1] = 1;
        body[3..11].copy_from_slice(&5u64.to_be_bytes());
        assert_eq!(candidate(&body), None);
    }
    #[test]
    fn argument_skipping_is_iterative_and_checks_lengths() {
        let mut body = Vec::new();
        for _ in 0..10000 {
            body.push(5);
            body.extend_from_slice(&1u64.to_be_bytes());
        }
        body.push(0);
        let mut bytes = body.as_slice();
        assert_eq!(skip(&mut bytes), Some(()));
        assert!(bytes.is_empty());
        let mut bytes = &[5, 255, 255, 255, 255, 255, 255, 255, 255][..];
        assert_eq!(skip(&mut bytes), None);
    }
}

/// Start one fixed batch and emit in input order. No refill. If emission fails,
/// scope exit still joins every already-started worker before returning failure.
pub(super) fn execute<T: Send, R: Send>(
    jobs: Vec<T>,
    worker: impl Fn(T) -> R + Sync,
    mut emit: impl FnMut(R) -> super::Result<()>,
) -> super::Result<()> {
    std::thread::scope(|scope| {
        let worker = &worker;
        let mut handles = Vec::new();
        let mut failure = None;
        for job in jobs {
            match std::thread::Builder::new()
                .name("jaydb2-read".into())
                .spawn_scoped(scope, move || worker(job))
            {
                Ok(handle) => handles.push(handle),
                Err(error) => {
                    failure = Some(error.into());
                    break;
                }
            }
        }
        for handle in handles {
            // Always explicitly join, including after failure, so a later panic
            // cannot mask the original channel error during implicit scope join.
            let result = handle
                .join()
                .map_err(|_| super::Error::new("READ_WORKER", "read worker panicked"));
            if failure.is_none()
                && let Err(error) = result.and_then(&mut emit)
            {
                failure = Some(error);
            }
        }
        failure.map_or(Ok(()), Err)
    })
}

#[cfg(test)]
mod execution_tests {
    use super::execute;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Barrier, Mutex, mpsc};

    #[test]
    fn workers_overlap_and_reverse_completion_emits_fifo() {
        let started = Barrier::new(2);
        let (tx, rx) = mpsc::channel();
        let rx = Mutex::new(rx);
        let mut emitted = Vec::new();
        execute(
            vec![0, 1],
            |index| {
                started.wait(); // Serial execution deadlocks; both must be active.
                if index == 0 {
                    rx.lock().unwrap().recv().unwrap();
                } else {
                    tx.send(()).unwrap();
                }
                index
            },
            |result| {
                emitted.push(result);
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(emitted, [0, 1]);
    }

    #[test]
    fn delivery_failure_stops_emission_and_drains_an_active_read() {
        let started = Barrier::new(2);
        let active = AtomicUsize::new(0);
        let (tx, rx) = mpsc::channel();
        let rx = Mutex::new(rx);
        let mut emitted = Vec::new();
        let result = execute(
            vec![0, 1],
            |index| {
                active.fetch_add(1, Ordering::SeqCst);
                started.wait();
                if index == 1 {
                    rx.lock().unwrap().recv().unwrap();
                }
                active.fetch_sub(1, Ordering::SeqCst);
                index
            },
            |result| {
                emitted.push(result);
                assert_eq!(active.load(Ordering::SeqCst), 1);
                tx.send(()).unwrap(); // The read remains active until failure here.
                Err(super::super::Error::new(
                    "TEST_DELIVERY",
                    "injected write failure",
                ))
            },
        );
        assert_eq!(result.unwrap_err().code, "TEST_DELIVERY");
        assert_eq!(emitted, [0]);
        assert_eq!(active.load(Ordering::SeqCst), 0);
    }
}

pub(super) trait Service: super::SerialService {
    fn max_readers(&self) -> usize;
    fn is_read(&self, body: &[u8]) -> bool;
    fn reads(
        &mut self,
        bodies: Vec<Vec<u8>>,
        output: &mut impl std::io::Write,
    ) -> super::Result<()>;
}

pub(super) fn coordinate(
    queue: &super::FrameQueue,
    output: &mut impl std::io::Write,
    service: &mut impl Service,
) -> super::Result<()> {
    use super::scheduling::{FrameEvent, InputEnd};
    loop {
        let response = match queue.select() {
            FrameEvent::Request(body) => {
                // A certified read borrows the already-published durable root
                // even when its fixed group contains one request. Reader count
                // controls overlap, not whether an unchanged root needs another
                // commit. Full authentication and native validation still run
                // inside Service::reads; this selection grants no authority.
                if service.is_read(&body) {
                    let mut batch = vec![body];
                    while batch.len() < service.max_readers() {
                        match queue.select_if(|next| service.is_read(next)) {
                            Some(next) => batch.push(next),
                            None => break,
                        }
                    }
                    service.reads(batch, output)?;
                    continue;
                }
                let completed = service.execute(&body);
                drop(body);
                service.publish(completed)?
            }
            FrameEvent::End(InputEnd::Eof) => return Ok(()),
            FrameEvent::End(InputEnd::Failed(error)) => return Err(error),
            FrameEvent::End(InputEnd::Framing(status)) => {
                output.write_all(&super::error_frame(status))?;
                output.flush()?;
                return Ok(());
            }
        };
        output.write_all(&response)?;
        output.flush()?;
    }
}

#[cfg(test)]
mod coordinator_tests {
    use super::*;
    use crate::scheduling::{FrameQueue, QueueBounds};
    use crate::{Result, SerialService, packet};
    use std::io::{self, Cursor, Write};

    struct Model {
        readers: usize,
        credential: u8,
        registered: bool,
        batches: Vec<Vec<Vec<u8>>>,
        exclusive: Vec<Vec<u8>>,
    }
    impl Model {
        fn new() -> Self {
            Self {
                readers: 2,
                credential: b'a',
                registered: true,
                batches: vec![],
                exclusive: vec![],
            }
        }
    }
    impl SerialService for Model {
        type Completion = Vec<u8>;
        fn execute(&mut self, body: &[u8]) -> Vec<u8> {
            self.exclusive.push(body.to_vec());
            body.to_vec()
        }
        fn publish(&mut self, body: Vec<u8>) -> Result<Vec<u8>> {
            match body[0] {
                b'w' => self.credential = body[1],
                b'i' => self.registered = false,
                _ => {}
            }
            Ok(vec![body[0]])
        }
    }
    impl Service for Model {
        fn max_readers(&self) -> usize {
            self.readers
        }
        fn is_read(&self, body: &[u8]) -> bool {
            self.registered && body[0] == b'r'
        }
        fn reads(&mut self, bodies: Vec<Vec<u8>>, output: &mut impl Write) -> Result<()> {
            self.batches.push(bodies.clone());
            let snapshot = self.credential;
            execute(
                bodies,
                |body| if body[1] == snapshot { snapshot } else { b'!' },
                |response| {
                    output.write_all(&[response])?;
                    output.flush()?;
                    Ok(())
                },
            )
        }
    }
    fn queue(bodies: &[&[u8]]) -> FrameQueue {
        let data = bodies.iter().flat_map(|body| packet(body, &[])).collect();
        let queue = FrameQueue::start(
            Cursor::new(data),
            2,
            QueueBounds {
                items: 16,
                bytes: 32,
            },
        )
        .unwrap();
        queue.wait_for_end();
        queue
    }
    #[test]
    fn fixed_head_batches_do_not_bypass_writes_and_reauthenticate_after_rotation_and_invalidation()
    {
        let queue = queue(&[b"ra", b"ra", b"wb", b"ra", b"rb", b"i", b"rb"]);
        let mut model = Model::new();
        let mut output = Vec::new();
        coordinate(&queue, &mut output, &mut model).unwrap();
        assert_eq!(output, b"aaw!bir");
        assert_eq!(
            model.batches,
            [
                vec![b"ra".to_vec(), b"ra".to_vec()],
                vec![b"ra".to_vec(), b"rb".to_vec()]
            ]
        );
        assert_eq!(
            model.exclusive,
            [b"wb".to_vec(), b"i".to_vec(), b"rb".to_vec()]
        );
    }
    #[test]
    fn one_reader_uses_certified_groups_and_preserves_write_and_control_barriers() {
        let queue = queue(&[b"ra", b"ra", b"wb", b"ra", b"rb", b"i", b"rb"]);
        let mut model = Model::new();
        model.readers = 1;
        let mut output = Vec::new();
        coordinate(&queue, &mut output, &mut model).unwrap();
        assert_eq!(output, b"aaw!bir");
        assert_eq!(
            model.batches,
            [
                vec![b"ra".to_vec()],
                vec![b"ra".to_vec()],
                vec![b"ra".to_vec()],
                vec![b"rb".to_vec()],
            ]
        );
        assert_eq!(
            model.exclusive,
            [b"wb".to_vec(), b"i".to_vec(), b"rb".to_vec()]
        );
    }
    #[test]
    fn terminal_framing_error_waits_for_the_complete_read_batch() {
        let data = [packet(b"ra", &[]), packet(b"ra", &[]), vec![0]].concat();
        let queue =
            FrameQueue::start(Cursor::new(data), 2, QueueBounds { items: 4, bytes: 4 }).unwrap();
        queue.wait_for_end();
        let mut model = Model::new();
        let mut output = Vec::new();
        coordinate(&queue, &mut output, &mut model).unwrap();
        assert_eq!(
            output,
            [b"aa".to_vec(), crate::error_frame("input")].concat()
        );
        assert_eq!(model.batches.len(), 1);
        assert!(model.exclusive.is_empty());
    }

    struct FailFlush;
    impl Write for FailFlush {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            Ok(bytes.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            Err(io::ErrorKind::BrokenPipe.into())
        }
    }
    #[test]
    fn failed_read_emission_never_starts_queued_exclusive_work() {
        let queue = queue(&[b"ra", b"ra", b"wb", b"ra"]);
        let mut model = Model::new();
        assert!(coordinate(&queue, &mut FailFlush, &mut model).is_err());
        assert_eq!(model.batches.len(), 1);
        assert!(model.exclusive.is_empty());
        assert_eq!(queue.select_if(|_| true).unwrap(), b"wb");
    }
}

#[cfg(test)]
mod pipe_failure_tests {
    use super::*;
    use crate::capture::{Pipe, inject_failure};
    use crate::scheduling::{FrameQueue, QueueBounds};
    use crate::{Result, SerialService, packet};
    use std::io::{Cursor, Write};
    use std::process::Command;

    struct Failure {
        point: Pipe,
        exclusive_started: usize,
    }
    impl SerialService for Failure {
        type Completion = Vec<u8>;
        fn execute(&mut self, body: &[u8]) -> Vec<u8> {
            self.exclusive_started += 1;
            body.to_vec()
        }
        fn publish(&mut self, response: Vec<u8>) -> Result<Vec<u8>> {
            Ok(response)
        }
    }
    impl Service for Failure {
        fn max_readers(&self) -> usize {
            2
        }
        fn is_read(&self, body: &[u8]) -> bool {
            body == b"read"
        }
        fn reads(&mut self, bodies: Vec<Vec<u8>>, _: &mut impl Write) -> Result<()> {
            execute(
                bodies,
                |_| inject_failure(Command::new("/bin/sleep").arg("30"), &[0; 8192], self.point),
                |_| Ok(()),
            )
        }
    }

    #[test]
    fn every_pipe_failure_stops_the_actual_coordinator_before_queued_exclusive_work() {
        for point in [Pipe::Input, Pipe::Output, Pipe::Error] {
            let bytes = [
                packet(b"read", &[]),
                packet(b"read", &[]),
                packet(b"write", &[]),
            ]
            .concat();
            let mut queue = FrameQueue::start(
                Cursor::new(bytes),
                5,
                QueueBounds {
                    items: 4,
                    bytes: 16,
                },
            )
            .unwrap();
            queue.wait_for_end();
            let mut service = Failure {
                point,
                exclusive_started: 0,
            };
            let mut output = Vec::new();
            assert_eq!(
                coordinate(&queue, &mut output, &mut service)
                    .unwrap_err()
                    .code,
                "READ_WORKER"
            );
            assert_eq!(service.exclusive_started, 0);
            assert!(output.is_empty());
            queue.close().unwrap();
        }
    }
}
