//! Bounded framing only. This reader never authenticates, executes or writes output.
//! The owner selects FIFO work, completes it, then emits before selecting again.
use std::collections::VecDeque;
use std::io;
use std::os::fd::AsRawFd;
use std::os::unix::net::UnixStream;
use std::sync::{Arc, Condvar, Mutex};
use std::thread::{self, JoinHandle};

#[derive(Clone, Copy, Debug)]
pub struct QueueBounds {
    pub items: usize,
    pub bytes: usize,
}

impl QueueBounds {
    pub fn for_message_limit(limit: u64) -> Self {
        // A logical uint64 limit is valid even beyond the host address space.
        // This is an accounting ceiling, not an upfront allocation.
        let bytes = limit.min(isize::MAX as u64) as usize;
        Self {
            items: 8,
            bytes: bytes.max(1024 * 1024),
        }
    }
}

/// Terminal events occupy one fixed slot after every complete frame.
#[derive(Debug)]
pub enum InputEnd {
    Eof,
    Framing(&'static str),
    Failed(crate::Error),
}

#[derive(Debug)]
pub enum FrameEvent {
    Request(Vec<u8>),
    End(InputEnd),
}

/// `execute` returns only after the entire proposal/response and worker cleanup
/// are complete. The service (including handles) stays coordinator-owned.
/// `publish` owns state publication; successful return is response-ready.
/// Fatal publication errors cause no response and no subsequent selection.
pub trait SerialService {
    type Completion;
    fn execute(&mut self, body: &[u8]) -> Self::Completion;
    fn publish(&mut self, completion: Self::Completion) -> crate::Result<Vec<u8>>;
}

#[cfg(test)]
pub fn coordinate(
    queue: &FrameQueue,
    output: &mut impl io::Write,
    service: &mut impl SerialService,
    terminal_response: impl Fn(&str) -> Vec<u8>,
) -> crate::Result<()> {
    loop {
        let (response, terminal) = match queue.select() {
            FrameEvent::Request(body) => {
                let completed = service.execute(&body);
                drop(body);
                (service.publish(completed)?, false)
            }
            FrameEvent::End(InputEnd::Eof) => return Ok(()),
            FrameEvent::End(InputEnd::Failed(error)) => return Err(error),
            FrameEvent::End(InputEnd::Framing(status)) => (terminal_response(status), true),
        };
        output.write_all(&response)?;
        output.flush()?;
        if terminal {
            return Ok(());
        }
    }
}

/// Reads must return when `cancel` becomes readable/hangs up. Only the framing
/// thread reads the input; no buffering may consume bytes beyond the given slice.
pub trait FrameInput: Send + 'static {
    fn read(&mut self, buffer: &mut [u8], cancel: &UnixStream) -> io::Result<usize>;
}

/// Linux/Unix descriptor adapter. The cancellation pipe wakes even with an open,
/// idle stdin, avoiding a leaked reader thread after delivery failure.
pub struct PollInput<R>(pub R);

impl<R: AsRawFd + Send + 'static> FrameInput for PollInput<R> {
    fn read(&mut self, buffer: &mut [u8], cancel: &UnixStream) -> io::Result<usize> {
        loop {
            let mut descriptors = [
                libc::pollfd {
                    fd: self.0.as_raw_fd(),
                    events: libc::POLLIN,
                    revents: 0,
                },
                libc::pollfd {
                    fd: cancel.as_raw_fd(),
                    events: libc::POLLIN,
                    revents: 0,
                },
            ];
            // SAFETY: both live descriptors and the writable array outlive poll.
            let result = unsafe { libc::poll(descriptors.as_mut_ptr(), 2, -1) };
            if result < 0 {
                let error = io::Error::last_os_error();
                if error.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(error);
            }
            if descriptors[1].revents != 0 {
                return Err(io::ErrorKind::ConnectionAborted.into());
            }
            if descriptors[0].revents != 0 {
                // Bypass Stdin's hidden BufReader: polling an empty descriptor
                // while it retains bytes would otherwise stall the protocol.
                // SAFETY: the live fd and writable buffer outlive this read;
                // this adapter is the sole reader of the descriptor.
                let count = unsafe {
                    libc::read(self.0.as_raw_fd(), buffer.as_mut_ptr().cast(), buffer.len())
                };
                return if count < 0 {
                    Err(io::Error::last_os_error())
                } else {
                    Ok(count as usize)
                };
            }
        }
    }
}

#[derive(Default)]
struct State {
    frames: VecDeque<Vec<u8>>,
    // Include the reader's reservation, BEFORE allocating/reading its body.
    items: usize,
    bytes: usize,
    end: Option<InputEnd>,
    stopped: bool,
}

#[derive(Default)]
struct Shared {
    state: Mutex<State>,
    changed: Condvar,
}

pub struct FrameQueue {
    shared: Arc<Shared>,
    cancel: Option<UnixStream>,
    reader: Option<JoinHandle<()>>,
}

impl FrameQueue {
    pub fn start(input: impl FrameInput, limit: u64, bounds: QueueBounds) -> io::Result<Self> {
        if bounds.items == 0
            || (bounds.bytes as u64) < limit.min(isize::MAX as u64)
            || bounds.bytes > isize::MAX as usize
        {
            return Err(io::Error::other(
                "queue must hold at least one maximum allocatable frame",
            ));
        }
        let shared = Arc::new(Shared::default());
        let (cancel, wake) = UnixStream::pair()?;
        let producer = shared.clone();
        let reader = thread::Builder::new()
            .name("jaydb2-framing".into())
            .spawn(move || {
                let end = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    receive(input, &wake, limit, bounds, &producer)
                }))
                .unwrap_or_else(|_| {
                    InputEnd::Failed(io::Error::other("framing reader panicked").into())
                });
                let mut state = producer.state.lock().unwrap();
                state.items = state.frames.len();
                state.bytes = state.frames.iter().map(Vec::len).sum();
                state.end = Some(end);
                producer.changed.notify_all();
            })?;
        Ok(Self {
            shared,
            cancel: Some(cancel),
            reader: Some(reader),
        })
    }

    /// Selection releases queue capacity. The owner now accounts for this one
    /// active request. The terminal event is selected only after all frames.
    pub fn select(&self) -> FrameEvent {
        let mut state = self.shared.state.lock().unwrap();
        loop {
            if let Some(body) = state.frames.pop_front() {
                state.items -= 1;
                state.bytes -= body.len();
                self.shared.changed.notify_all();
                return FrameEvent::Request(body);
            }
            if let Some(end) = state.end.take() {
                return FrameEvent::End(end);
            }
            state = self.shared.changed.wait(state).unwrap();
        }
    }

    #[cfg(test)]
    pub fn wait_for_end(&self) {
        let (state, timeout) = self
            .shared
            .changed
            .wait_timeout_while(
                self.shared.state.lock().unwrap(),
                std::time::Duration::from_secs(5),
                |state| state.end.is_none(),
            )
            .unwrap();
        assert!(
            !timeout.timed_out() || state.end.is_some(),
            "input completion timed out"
        );
    }

    /// Select only an already-enqueued qualifying head. Never skip a barrier,
    /// consume a terminal event, or wait for a batch to fill.
    pub fn select_if(&self, eligible: impl FnOnce(&[u8]) -> bool) -> Option<Vec<u8>> {
        let mut state = self.shared.state.lock().unwrap();
        if !state.frames.front().is_some_and(|body| eligible(body)) {
            return None;
        }
        let body = state.frames.pop_front().expect("checked head");
        state.items -= 1;
        state.bytes -= body.len();
        self.shared.changed.notify_all();
        Some(body)
    }

    /// Cancel blocked reads/capacity waits and join the sole owned reader.
    pub fn close(&mut self) -> io::Result<()> {
        {
            let mut state = self.shared.state.lock().unwrap();
            state.stopped = true;
            self.shared.changed.notify_all();
        }
        // HUP is part of FrameInput's cancellation contract. Drop the sole
        // sender before joining, with no fallible wakeup that can bypass join.
        drop(self.cancel.take());
        if let Some(reader) = self.reader.take() {
            reader
                .join()
                .map_err(|_| io::Error::other("framing reader failed"))?;
        }
        Ok(())
    }
}

impl Drop for FrameQueue {
    fn drop(&mut self) {
        let _ = self.close();
    }
}

fn read_up_to(
    input: &mut impl FrameInput,
    cancel: &UnixStream,
    mut buffer: &mut [u8],
) -> io::Result<usize> {
    let expected = buffer.len();
    while !buffer.is_empty() {
        match input.read(buffer, cancel) {
            Ok(0) => break,
            Ok(quantity) => buffer = &mut buffer[quantity..],
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(error),
        }
    }
    Ok(expected - buffer.len())
}

fn receive(
    mut input: impl FrameInput,
    cancel: &UnixStream,
    limit: u64,
    bounds: QueueBounds,
    shared: &Shared,
) -> InputEnd {
    let read = |input: &mut _, buffer: &mut [u8]| read_up_to(input, cancel, buffer);
    loop {
        {
            let mut state = shared.state.lock().unwrap();
            while !state.stopped && state.items == bounds.items {
                state = shared.changed.wait(state).unwrap();
            }
            if state.stopped {
                return InputEnd::Eof;
            }
            state.items += 1;
            shared.changed.notify_all();
        }
        let mut header = [0; 8];
        match read(&mut input, &mut header) {
            Ok(0) => return InputEnd::Eof,
            Ok(8) => (),
            Ok(_) => return InputEnd::Framing("input"),
            Err(error) => return InputEnd::Failed(error.into()),
        }
        let size = u64::from_be_bytes(header);
        if size > limit {
            return InputEnd::Framing("limit");
        }
        let size = match usize::try_from(size) {
            Ok(size) if size <= isize::MAX as usize => size,
            _ => {
                return InputEnd::Failed(crate::Error::new(
                    "HOST_TRANSPORT",
                    "message length is not allocatable",
                ));
            }
        };
        {
            let mut state = shared.state.lock().unwrap();
            shared.changed.notify_all();
            while !state.stopped && size > bounds.bytes - state.bytes {
                state = shared.changed.wait(state).unwrap();
            }
            if state.stopped {
                return InputEnd::Eof;
            }
            state.bytes += size;
            shared.changed.notify_all();
        }
        let mut body = Vec::new();
        if body.try_reserve_exact(size).is_err() {
            return InputEnd::Failed(crate::Error::new(
                "HOST_TRANSPORT",
                "cannot allocate message body",
            ));
        }
        body.resize(size, 0);
        match read(&mut input, &mut body) {
            Ok(quantity) if quantity == size => (),
            Ok(_) => return InputEnd::Framing("input"),
            Err(error) => return InputEnd::Failed(error.into()),
        }
        let mut state = shared.state.lock().unwrap();
        if state.stopped {
            return InputEnd::Eof;
        }
        state.frames.push_back(body);
        shared.changed.notify_all();
    }
}

#[cfg(test)]
impl FrameInput for io::Cursor<Vec<u8>> {
    fn read(&mut self, buffer: &mut [u8], _: &UnixStream) -> io::Result<usize> {
        io::Read::read(self, buffer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Error, Result, error_frame, packet};
    use std::io::{Cursor, Read, Write};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Duration;

    fn wait(queue: &FrameQueue, predicate: impl Fn(&State) -> bool) {
        let (state, timeout) = queue
            .shared
            .changed
            .wait_timeout_while(
                queue.shared.state.lock().unwrap(),
                Duration::from_secs(5),
                |state| !predicate(state),
            )
            .unwrap();
        assert!(
            !timeout.timed_out() || predicate(&state),
            "queue progress timed out"
        );
    }

    fn take(queue: &FrameQueue) -> Vec<u8> {
        match queue.select() {
            FrameEvent::Request(body) => body,
            other => panic!("expected frame, got {other:?}"),
        }
    }

    struct ObservedInput {
        bytes: Cursor<Vec<u8>>,
        consumed: Arc<AtomicUsize>,
    }

    impl FrameInput for ObservedInput {
        fn read(&mut self, buffer: &mut [u8], _: &UnixStream) -> io::Result<usize> {
            let count = Read::read(&mut self.bytes, buffer)?;
            self.consumed.fetch_add(count, Ordering::SeqCst);
            Ok(count)
        }
    }

    #[test]
    fn bytes_reserved_before_body_read_and_item_backpressure_includes_empty_frames() {
        let consumed = Arc::new(AtomicUsize::new(0));
        let input = ObservedInput {
            bytes: Cursor::new(
                [packet(b"abcd", &[]), packet(b"efgh", &[]), packet(b"", &[])].concat(),
            ),
            consumed: consumed.clone(),
        };
        let queue = FrameQueue::start(input, 4, QueueBounds { items: 2, bytes: 4 }).unwrap();
        // Second header fits, but no byte of its body can be consumed until
        // selection releases the first body. No scheduler sleeps or races.
        wait(&queue, |s| s.frames.len() == 1 && s.items == 2);
        wait(&queue, |s| {
            s.frames.len() == 1 && s.items == 2 && consumed.load(Ordering::SeqCst) == 20
        });
        assert_eq!(queue.shared.state.lock().unwrap().bytes, 4);
        assert_eq!(take(&queue), b"abcd");
        wait(&queue, |s| s.frames.len() == 2);
        {
            let state = queue.shared.state.lock().unwrap();
            assert_eq!((state.items, state.bytes), (2, 4));
            assert!(
                state.end.is_none(),
                "full queue must not read another header"
            );
            assert_eq!(consumed.load(Ordering::SeqCst), 32);
        }
        assert_eq!(take(&queue), b"efgh");
        assert_eq!(take(&queue), b"");
        assert!(matches!(queue.select(), FrameEvent::End(InputEnd::Eof)));
    }

    #[test]
    fn terminal_eof_partial_header_partial_body_and_oversize_follow_all_complete_frames() {
        let mut endings = vec![
            (vec![], None),
            (5u64.to_be_bytes().to_vec(), Some("limit")),
            (u64::MAX.to_be_bytes().to_vec(), Some("limit")),
        ];
        for size in 1..8 {
            endings.push((vec![0; size], Some("input")));
        }
        for size in 0..4 {
            endings.push((
                [4u64.to_be_bytes().to_vec(), vec![0; size]].concat(),
                Some("input"),
            ));
        }
        for (ending, expected) in endings {
            let input = Cursor::new([packet(b"one", &[]), packet(b"two", &[]), ending].concat());
            let queue = FrameQueue::start(
                input,
                4,
                QueueBounds {
                    items: 4,
                    bytes: 12,
                },
            )
            .unwrap();
            // Ensure the read-ahead terminal is known BEFORE any selection.
            wait(&queue, |s| s.end.is_some());
            assert_eq!(take(&queue), b"one");
            assert_eq!(take(&queue), b"two");
            match (queue.select(), expected) {
                (FrameEvent::End(InputEnd::Eof), None) => (),
                (FrameEvent::End(InputEnd::Framing(actual)), Some(expected)) => {
                    assert_eq!(actual, expected)
                }
                other => panic!("unexpected terminal: {other:?}"),
            }
        }
    }

    struct FragmentedInput {
        bytes: Cursor<Vec<u8>>,
        interrupt: bool,
    }
    impl FrameInput for FragmentedInput {
        fn read(&mut self, buffer: &mut [u8], _: &UnixStream) -> io::Result<usize> {
            self.interrupt = !self.interrupt;
            if self.interrupt {
                return Err(io::ErrorKind::Interrupted.into());
            }
            if self.bytes.position() == self.bytes.get_ref().len() as u64 {
                return Err(io::Error::other("controlled input failure"));
            }
            Read::read(&mut self.bytes, &mut buffer[..1])
        }
    }

    #[test]
    fn fragmented_interrupted_input_and_read_failure_preserve_complete_requests() {
        let input = FragmentedInput {
            bytes: Cursor::new(packet(b"ok", &[])),
            interrupt: false,
        };
        let queue = FrameQueue::start(input, 2, QueueBounds { items: 2, bytes: 2 }).unwrap();
        wait(&queue, |s| s.end.is_some());
        let mut service = Service::default();
        let mut output = Vec::new();
        let error = coordinate(&queue, &mut output, &mut service, error_frame).unwrap_err();
        assert!(error.message.contains("controlled input failure"));
        assert_eq!(service.selected, [b"ok".to_vec()]);
        assert_eq!(output, b"ok");
    }

    #[derive(Default)]
    struct Service {
        selected: Vec<Vec<u8>>,
        published: usize,
        fatal: bool,
    }
    impl SerialService for Service {
        type Completion = Vec<u8>;
        fn execute(&mut self, body: &[u8]) -> Vec<u8> {
            self.selected.push(body.to_vec());
            body.to_vec()
        }
        fn publish(&mut self, completed: Vec<u8>) -> Result<Vec<u8>> {
            self.published += 1;
            if self.fatal {
                return Err(Error::new("COMMIT_UNCERTAIN", "controlled fatal commit"));
            }
            Ok(completed)
        }
    }

    #[test]
    fn fatal_publication_emits_nothing_and_never_selects_the_next_request() {
        let queue = FrameQueue::start(
            Cursor::new([packet(b"a", &[]), packet(b"b", &[])].concat()),
            1,
            QueueBounds { items: 3, bytes: 2 },
        )
        .unwrap();
        wait(&queue, |s| s.end.is_some());
        let mut service = Service {
            fatal: true,
            ..Service::default()
        };
        let mut output = Vec::new();
        assert_eq!(
            coordinate(&queue, &mut output, &mut service, error_frame)
                .unwrap_err()
                .code,
            "COMMIT_UNCERTAIN"
        );
        assert!(output.is_empty());
        assert_eq!(service.selected, [b"a".to_vec()]);
        assert_eq!(take(&queue), b"b");
    }

    struct FailingOutput {
        bytes: Vec<u8>,
        fail_after: usize,
        fail_flush: bool,
    }
    impl Write for FailingOutput {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            let count = bytes.len().min(self.fail_after - self.bytes.len());
            if count == 0 {
                return Err(io::ErrorKind::BrokenPipe.into());
            }
            self.bytes.extend_from_slice(&bytes[..count]);
            Ok(count)
        }
        fn flush(&mut self) -> io::Result<()> {
            if self.fail_flush {
                Err(io::ErrorKind::BrokenPipe.into())
            } else {
                Ok(())
            }
        }
    }

    #[test]
    fn partial_write_and_flush_failures_stop_dispatch_without_undo_or_retry() {
        for (fail_after, fail_flush, expected) in [
            (0, false, b"".as_slice()),
            (1, false, b"o"),
            (2, true, b"ok"),
        ] {
            let queue = FrameQueue::start(
                Cursor::new([packet(b"ok", &[]), packet(b"no", &[])].concat()),
                2,
                QueueBounds { items: 3, bytes: 4 },
            )
            .unwrap();
            wait(&queue, |s| s.end.is_some());
            let mut service = Service::default();
            let mut output = FailingOutput {
                bytes: Vec::new(),
                fail_after,
                fail_flush,
            };
            assert!(coordinate(&queue, &mut output, &mut service, error_frame).is_err());
            assert_eq!(output.bytes, expected);
            assert_eq!(service.selected, [b"ok".to_vec()]);
            assert_eq!(service.published, 1);
            assert_eq!(take(&queue), b"no");
        }
    }

    #[test]
    fn cancel_joins_reader_blocked_in_header_body_or_capacity_with_input_still_open() {
        for (bytes, full) in [
            (vec![], false),
            (4u64.to_be_bytes().to_vec(), false),
            (packet(b"full", &[]), true),
        ] {
            let (mut writer, reader) = UnixStream::pair().unwrap();
            writer.write_all(&bytes).unwrap();
            let mut queue =
                FrameQueue::start(PollInput(reader), 4, QueueBounds { items: 1, bytes: 4 })
                    .unwrap();
            wait(&queue, |s| {
                if full {
                    s.frames.len() == 1
                } else if bytes.is_empty() {
                    s.items == 1
                } else {
                    s.bytes == 4
                }
            });
            // A bounded timeout is a test guard, never a server deadline.
            let (tx, rx) = std::sync::mpsc::channel();
            let joined = thread::spawn(move || {
                queue.close().unwrap();
                assert!(queue.reader.is_none());
                tx.send(()).unwrap();
            });
            rx.recv_timeout(Duration::from_secs(5))
                .expect("reader failed to cancel");
            joined.join().unwrap();
            drop(writer);
        }
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn cancellation_drops_endpoint_and_joins_when_shutdown_is_denied() {
        const CHILD: &str = "JAYDB_SCHEDULING_CANCEL_TEST_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "scheduling::tests::cancellation_drops_endpoint_and_joins_when_shutdown_is_denied", "--nocapture"])
                .env(CHILD, "1")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "isolated cancellation test failed: {}\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            return;
        }
        // The filter is confined to this isolated child. The descriptors stay
        // valid and connected; only the real shutdown syscall returns EPERM.
        let mut rules = [
            libc::sock_filter {
                code: (libc::BPF_LD | libc::BPF_W | libc::BPF_ABS) as u16,
                jt: 0,
                jf: 0,
                k: 0,
            },
            libc::sock_filter {
                code: (libc::BPF_JMP | libc::BPF_JEQ | libc::BPF_K) as u16,
                jt: 0,
                jf: 1,
                k: libc::SYS_shutdown as u32,
            },
            libc::sock_filter {
                code: (libc::BPF_RET | libc::BPF_K) as u16,
                jt: 0,
                jf: 0,
                k: libc::SECCOMP_RET_ERRNO | libc::EPERM as u32,
            },
            libc::sock_filter {
                code: (libc::BPF_RET | libc::BPF_K) as u16,
                jt: 0,
                jf: 0,
                k: libc::SECCOMP_RET_ALLOW,
            },
        ];
        let program = libc::sock_fprog {
            len: rules.len() as u16,
            filter: rules.as_mut_ptr(),
        };
        // SAFETY: these scalar arguments install no-new-privileges only in
        // this child test thread; no process outside it is affected.
        assert_eq!(
            unsafe { libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) },
            0
        );
        // SAFETY: the live program and instruction slice outlive prctl; the
        // kernel copies them before returning. Other syscalls remain allowed.
        assert_eq!(
            unsafe { libc::prctl(libc::PR_SET_SECCOMP, libc::SECCOMP_MODE_FILTER, &program) },
            0
        );
        let (writer, reader) = UnixStream::pair().unwrap();
        let mut queue =
            FrameQueue::start(PollInput(reader), 1, QueueBounds { items: 1, bytes: 1 }).unwrap();
        wait(&queue, |state| state.items == 1);
        let result = queue.close();
        assert!(
            result.is_ok(),
            "cleanup returned before joining: {result:?}"
        );
        assert!(queue.reader.is_none());
        queue.close().unwrap();
        drop(writer);
    }

    #[test]
    fn bounds_hold_allocatable_messages_without_restricting_canonical_limits() {
        assert_eq!(QueueBounds::for_message_limit(0).bytes, 1024 * 1024);
        assert_eq!(
            QueueBounds::for_message_limit(2 * 1024 * 1024).bytes,
            2 * 1024 * 1024
        );
        assert_eq!(
            QueueBounds::for_message_limit(u64::MAX).bytes,
            isize::MAX as usize
        );
        for bounds in [
            QueueBounds { items: 0, bytes: 4 },
            QueueBounds { items: 1, bytes: 3 },
        ] {
            assert!(FrameQueue::start(Cursor::new(vec![]), 4, bounds).is_err());
        }
    }

    #[test]
    fn uint64_max_canonical_limit_serves_small_frames_without_large_allocation() {
        let input = Cursor::new(
            [
                packet(b"small", &[]),
                packet(b"", &[]),
                packet(b"next", &[]),
            ]
            .concat(),
        );
        let queue =
            FrameQueue::start(input, u64::MAX, QueueBounds::for_message_limit(u64::MAX)).unwrap();
        let mut service = Service::default();
        let mut output = Vec::new();
        coordinate(&queue, &mut output, &mut service, error_frame).unwrap();
        assert_eq!(
            service.selected,
            [b"small".to_vec(), vec![], b"next".to_vec()]
        );
        assert_eq!(output, b"smallnext");
    }

    #[test]
    fn unallocatable_body_is_ordered_technical_failure_and_never_a_false_logical_limit() {
        for size in [isize::MAX as u64 + 1, u64::MAX] {
            let input = Cursor::new([packet(b"ok", &[]), size.to_be_bytes().to_vec()].concat());
            let queue =
                FrameQueue::start(input, u64::MAX, QueueBounds::for_message_limit(u64::MAX))
                    .unwrap();
            wait(&queue, |s| s.end.is_some());
            let mut service = Service::default();
            let mut output = Vec::new();
            let error = coordinate(&queue, &mut output, &mut service, error_frame).unwrap_err();
            assert_eq!(error.code, "HOST_TRANSPORT");
            assert_eq!(output, b"ok");
            assert_eq!(service.selected, [b"ok".to_vec()]);
        }
    }

    #[test]
    fn controlled_execution_cleanup_and_delivery_gate_later_selection_and_terminal() {
        use std::sync::mpsc::{Receiver, Sender, channel};
        struct ControlledService {
            events: Sender<&'static str>,
            execute: Receiver<()>,
        }
        impl SerialService for ControlledService {
            type Completion = Vec<u8>;
            fn execute(&mut self, body: &[u8]) -> Vec<u8> {
                self.events.send("selected").unwrap();
                self.execute.recv().unwrap(); // controlled worker completion
                self.events.send("worker-cleaned").unwrap();
                body.to_vec()
            }
            fn publish(&mut self, body: Vec<u8>) -> Result<Vec<u8>> {
                self.events.send("response-ready").unwrap();
                Ok(body)
            }
        }
        struct ControlledOutput {
            events: Sender<&'static str>,
            emit: Receiver<()>,
            bytes: Vec<u8>,
        }
        impl Write for ControlledOutput {
            fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
                self.events.send("delivery-start").unwrap();
                self.emit.recv().unwrap(); // controlled blocked output
                self.bytes.extend_from_slice(bytes);
                Ok(bytes.len())
            }
            fn flush(&mut self) -> io::Result<()> {
                self.events.send("response-emitted").unwrap();
                Ok(())
            }
        }
        let queue = FrameQueue::start(
            Cursor::new([packet(b"a", &[]), packet(b"b", &[]), vec![0]].concat()),
            1,
            QueueBounds { items: 3, bytes: 2 },
        )
        .unwrap();
        wait(&queue, |s| s.end.is_some()); // terminal is detected before service
        let (events, observed) = channel();
        let (run, execute) = channel();
        let (deliver, emit) = channel();
        let coordinator = thread::spawn(move || {
            let mut service = ControlledService {
                events: events.clone(),
                execute,
            };
            let mut output = ControlledOutput {
                events,
                emit,
                bytes: vec![],
            };
            coordinate(&queue, &mut output, &mut service, error_frame).unwrap();
            output.bytes
        });
        let event = || observed.recv_timeout(Duration::from_secs(5)).unwrap();
        for _ in 0..2 {
            assert_eq!(event(), "selected");
            assert!(observed.try_recv().is_err(), "execution gate was bypassed");
            run.send(()).unwrap();
            assert_eq!(event(), "worker-cleaned");
            assert_eq!(event(), "response-ready");
            assert_eq!(event(), "delivery-start");
            assert!(
                observed.try_recv().is_err(),
                "next request selected before delivery"
            );
            deliver.send(()).unwrap();
            assert_eq!(event(), "response-emitted");
        }
        assert_eq!(event(), "delivery-start"); // terminal response, no execution
        deliver.send(()).unwrap();
        assert_eq!(event(), "response-emitted");
        assert_eq!(
            coordinator.join().unwrap(),
            [b"ab".to_vec(), error_frame("input")].concat()
        );
    }
}
