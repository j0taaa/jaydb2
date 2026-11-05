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
            0 | 1 | 2 => {}
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
        let handles: Vec<_> = jobs
            .into_iter()
            .map(|job| scope.spawn(move || worker(job)))
            .collect();
        let mut failure = None;
        for handle in handles {
            // Always explicitly join, including after failure, so a later panic
            // cannot mask the original channel error during implicit scope join.
            let result = handle
                .join()
                .map_err(|_| super::Error::new("READ_WORKER", "read worker panicked"));
            if failure.is_none() {
                if let Err(error) = result.and_then(&mut emit) {
                    failure = Some(error);
                }
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
                if service.max_readers() > 1 && service.is_read(&body) {
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
            FrameEvent::End(InputEnd::Failed(error)) => return Err(error.into()),
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
