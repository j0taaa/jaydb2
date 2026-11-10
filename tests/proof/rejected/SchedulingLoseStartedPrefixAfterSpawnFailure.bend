# A later spawn failure must not erase successful earlier FIFO replies.
import Base
import ../../../proof/FrameQueue.bend as Q
import ../../../proof/ReadBatchExecution.bend as B

def spawn(frame: Q.Frame) -> B.SpawnReturn:
  match frame:
    case Q.Frame{0n, body}: B.Started{}
    case Q.Frame{1n+identity, body}: B.SpawnError{"spawn failed"}

law false_later_spawn_failure_erases_the_completed_started_prefix:
  {B.attempted_jobs(B.attempts(B.execute(spawn, job => B.Joined{[]},
    job => response => B.Sent{}, [Q.Frame{0n, []}, Q.Frame{1n, []}]))) ==
      Nil{} : List<&2, Q.Frame>}
def false_later_spawn_failure_erases_the_completed_started_prefix():
  {==}
