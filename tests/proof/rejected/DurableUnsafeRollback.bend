import Base
import ../../../proof/DurableCommit.bend as C

law false:
  {C.commit(C.Returns{C.Succeeded{}, C.Succeeded{}, C.FailedAfter{}, C.Succeeded{}}) ==
   C.CommitFailed{False{}, C.Replaced{}} : C.CommitResult}
def false():
  {==}
