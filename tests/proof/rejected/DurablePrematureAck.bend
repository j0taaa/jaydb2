import Base
import ../../../proof/DurableCommit.bend as C

law false:
  {C.commit(C.Returns{C.Succeeded{}, C.Succeeded{}, C.Succeeded{}, C.FailedBefore{}}) ==
   C.CommitReady{C.Replaced{}} : C.CommitResult}
def false():
  {==}
