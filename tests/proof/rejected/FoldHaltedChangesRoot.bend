import Base
import ../../../contract/Theorems.bend as G
import ../../../contract/Semantics.bend as S
import ../../../contract/Protocol.bend as P
import ../Controls.bend as X

def rejected_bytes() -> List<&2, U32>:
  Maybe.default(&2, List<&2, U32>, P.frame(S.response_value(S.response_error(S.Certificate{}))), Nil{})

# A halted (rejected) step that feeds a changed root into the next step.
law false:
  G.Step<X.configuration(), X.seed(), X.request(), X.reject, X.changed()>
def false():
  G.StepHalted{S.response_error(S.Certificate{}), rejected_bytes(), {==}, {==}}
