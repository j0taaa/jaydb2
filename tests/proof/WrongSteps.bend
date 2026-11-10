import Base
import ../../contract/Data.bend as D
import ../../contract/Semantics.bend as S
import ../../contract/Protocol.bend as P
import ../../src/Core.bend as N
import ../../src/Gate.bend as K
import ./Controls.bend as X

def uncertified_begin() -> K.Entry:
  K.Started{X.context(), N.start(X.program(), X.context(), D.VAbsent{}, X.seed())}

def spoofed_begin() -> K.Entry:
  K.Started{X.spoof(), N.start(X.program(), X.spoof(), D.VAbsent{}, X.seed())}

def publishes_refusal() -> N.Conclusion:
  N.Conclusion{X.changed(), S.Response{S.Refusal{}, D.VAbsent{}}, Nil{}}

def is_accept(v: K.Verdict) -> Bool:
  match v:
    case K.Accept{p}: True{}
    case _: False{}

def is_spoof(m: Maybe<&2, D.Context>) -> Bool:
  match m:
    case Some{D.Context{id, kind}}: String.eq(id, "bob")
    case None{}: False{}

def has_users(s: D.State) -> Bool:
  match s:
    case D.State{tables, Nil{}}: False{}
    case D.State{tables, Con{head, tail}}: True{}

def accept(c: S.Configuration, r: P.Request, ctx: D.Context) -> K.Verdict:
  K.Accept{X.program()}

def is_halted(entry: K.Entry) -> Bool:
  match entry:
    case K.Halted{response}: True{}
    case K.Started{context, machine}: False{}

# A machine that stopped with the generic failure status.
def failed_machine() -> N.Machine:
  N.Stopped{X.seed(), Nil{}, S.response_error(S.Failure{})}

def failure_bytes() -> List<&2, U32>:
  Maybe.default(&2, List<&2, U32>, P.frame(S.response_value(S.response_error(S.Failure{}))), Nil{})
