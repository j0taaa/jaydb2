# A final reference trace still needs the actual preparation step. The wrapper
# cannot report arbitrary bytes by skipping that step, even for a refusal.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../proof/ExecutionAdapter.bend as A
import ../../../src/Core.bend as N
import ../../../src/Execution.bend as X

law false_skipping_preparation_still_emits_complete_response:
  for ~c: S.Configuration
  for initial: D.State
  for working: D.State
  for value: D.Value
  {A.drive(c, 0n, X.Prepare{X.StateExecution{initial,
    N.Stopped{working, Nil{}, S.Response{S.Refusal{}, value}}}}) ==
    X.FinishOutput{Nil{}} : X.Iteration}
def false_skipping_preparation_still_emits_complete_response(c, initial, working, value):
  {==}
