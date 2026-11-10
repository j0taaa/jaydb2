import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../src/Core.bend as N
import ../../../src/Execution.bend as X

law false:
  for state: D.State
  for value: D.Value
  for bytes: List<&2, U32>
  {X.decision(N.Conclusion{state, S.Response{S.Refusal{}, value}, bytes}) ==
    X.Commit{state, bytes} : X.Decision}
def false(state, value, bytes): {==}
