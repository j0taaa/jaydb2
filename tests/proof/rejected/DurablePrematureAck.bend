import Base
import ../../../proof/DurableCommit.bend as C

law false_can_acknowledge_before_directory_sync:
  {C.commit(C.Returns{C.Succeeded{}, C.Succeeded{}, C.Succeeded{}, C.FailedBefore{}}) ==
   C.CommitReady{C.Replaced{}} : C.CommitResult}
def false_can_acknowledge_before_directory_sync():
  {==}
