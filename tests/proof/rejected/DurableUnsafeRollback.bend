import Base
import ../../../proof/DurableCommit.bend as C

law false_replacement_error_is_a_safe_rollback:
  {C.commit(C.Returns{C.Succeeded{}, C.Succeeded{}, C.FailedAfter{}, C.Succeeded{}}) ==
   C.CommitFailed{False{}, C.Replaced{}} : C.CommitResult}
def false_replacement_error_is_a_safe_rollback():
  {==}
