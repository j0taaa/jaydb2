import Base
import ../../../proof/DurableCommit.bend as C

law false:
  {C.slot_commit(C.SlotReturns{C.Succeeded{}, C.Succeeded{}, C.FailedBefore{}}) ==
   C.CommitReady{C.RecordWritten{}} : C.CommitResult}
def false():
  {==}
