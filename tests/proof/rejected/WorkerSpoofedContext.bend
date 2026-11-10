import Base
import ../Controls.bend as C
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../src/Gate.bend as Gate
import ../../../src/Worker.bend as W
import ../../../src/Execution.bend as X

def observed(ctx: D.Context) -> S.Action:
  D.Context{id, kind} = ctx
  S.Finish{D.VText{id}}

def program() -> S.Program:
  S.Program{ctx => args => observed(ctx)}

law false:
  {W.entered(Gate.begin(C.configuration(), C.seed(), C.request(),
      c => r => ctx => Gate.Accept{program()}), C.seed()) ==
    X.Continue{X.start(program(), C.spoof(), Gate.arguments(C.request()), C.seed())} : X.Iteration}
def false(): {==}
