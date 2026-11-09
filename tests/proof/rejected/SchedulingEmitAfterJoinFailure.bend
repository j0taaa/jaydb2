# Regression: later successful workers cannot emit after an earlier join panic.
import Base
import ../../../proof/FrameQueue.bend as Q
import ../../../proof/ReadBatchExecution.bend as B

def joined(frame: Q.Frame) -> B.JoinReturn:
  match frame:
    case Q.Frame{0n, body}: B.JoinError{"worker panic"}
    case Q.Frame{1n+identity, body}: B.Joined{[]}

law false_reply_after_join_failure_is_emitted:
  {B.attempted_jobs(B.attempts(B.drain(joined,
    job => response => B.Sent{}, [Q.Frame{0n, []}, Q.Frame{1n, []}], None{}))) ==
      [Q.Frame{1n, []}] : List<&2, Q.Frame>}
def false_reply_after_join_failure_is_emitted():
  {==}
