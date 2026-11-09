# Regression: a prefix spawn failure is already recorded before any joins;
# every started handle is joined but even its successful reply is suppressed.
import Base
import ../../../proof/FrameQueue.bend as Q
import ../../../proof/ReadBatchExecution.bend as B

def spawn(frame: Q.Frame) -> B.SpawnReturn:
  match frame:
    case Q.Frame{0n, body}: B.Started{}
    case Q.Frame{1n+identity, body}: B.SpawnError{"spawn failed"}

law false_prefix_is_emitted_despite_later_spawn_failure:
  {B.attempted_jobs(B.attempts(B.execute(spawn, job => B.Joined{[]},
    job => response => B.Sent{}, [Q.Frame{0n, []}, Q.Frame{1n, []}]))) ==
      [Q.Frame{0n, []}] : List<&2, Q.Frame>}
def false_prefix_is_emitted_despite_later_spawn_failure():
  {==}
