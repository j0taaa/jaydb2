import Base
import ../Controls.bend as C
import ../../../contract/Semantics.bend as S
import ../../../src/Dispatch.bend as Dispatch
import ../../../src/Messages.bend as Messages

law correct_denial:
  {Dispatch.authenticated(Dispatch.received(S.limits(C.configuration()), [255], C.seed())) == Messages.error(S.Input{}) : List<&2, U32>}
def correct_denial(): {==}

law false:
  {Dispatch.authenticated(Dispatch.received(S.limits(C.configuration()), [255], C.seed())) == Messages.error(S.Authentication{}) : List<&2, U32>}
def false(): {==}
