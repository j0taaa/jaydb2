# Reusing canonical state bytes never converts success to Keep.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../src/Execution.bend as X

law false:
  {X.response_packet(Some{[9]}, S.Response{S.Success{}, D.VAbsent{}}, Some{[0]}) ==
    X.FinishOutput{[0, 9]} : X.Iteration}
def false():
  {==}
