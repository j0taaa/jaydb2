import Base
import ../../../proof/DurableCommit.bend as C

law false:
  {C.repair(C.RepairReturns{C.Succeeded{}, C.FailedBefore{}, C.Succeeded{}}) ==
   C.CommitReady{C.RecordWritten{}} : C.CommitResult}
def false():
  {==}
