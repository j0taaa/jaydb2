import Base
import ../Controls.bend as C
import ../../../contract/Data.bend as D
import ../../../contract/Protocol.bend as P
import ../../../contract/Semantics.bend as S
import ../../../contract/PreparedRegistry.bend as Registry
import ../../../src/Control.bend as Control
import ../../../src/Worker.bend as W
import ../../../src/Execution.bend as X
import ../../../src/Input.bend as Input
import ../../../src/Gate.bend as Gate

def worker() -> X.Iteration:
  W.registered(C.configuration(), C.seed(), Input.InputReady{C.seed(), P.Request{"token", "handle", D.VAbsent{}, ""}},
    [Registry.Entry{"controls", "handle", "program", "other-proof", False{}, ""}],
    W.artifact_oracle("program", "proof", c => r => ctx => Gate.Accept{C.program()}))

law correct_denial:
  {worker() == X.result(Gate.early(S.response_error(S.Failure{}), C.seed())) : X.Iteration}
def correct_denial(): {==}

law false:
  {worker() == X.Continue{X.start(C.program(), C.context(), D.VAbsent{}, C.seed())} : X.Iteration}
def false(): {==}
