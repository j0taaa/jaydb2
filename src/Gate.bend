# Executable authentication/admission gate; native host integration is separate.
# The actual transition/encoding functions below are imported unchanged.
import Base
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ./Core.bend as N

type Verdict is Type:
  Reject{}
  ToolFailure{}
  Accept{program: S.Program}

def Oracle() -> Type:
  S.Configuration -> P.Request -> D.Context -> Verdict

type Entry is Type:
  Halted{response: S.Response}
  Started{context: D.Context, machine: N.Machine}

def credential(r: P.Request) -> String:
  P.Request{credential, code, arguments, proof} = r
  credential

def code(r: P.Request) -> String:
  P.Request{credential, code, arguments, proof} = r
  code

def arguments(r: P.Request) -> D.Value:
  P.Request{credential, code, arguments, proof} = r
  arguments

def admitted(v: Verdict, +ctx: D.Context, args: D.Value, s: D.State) -> Entry:
  match v:
    case Reject{}: Halted{S.response_error(S.Certificate{})}
    case ToolFailure{}: Halted{S.response_error(S.Failure{})}
    case Accept{program}: Started{ctx, N.start(program, ctx, args, s)}

def authenticated(c: S.Configuration, ctx: Maybe<&2, D.Context>, +r: P.Request, s: D.State,
  admit: Oracle()) -> Entry:
  match ctx:
    case None{}: Halted{S.response_error(S.Authentication{})}
    case Some{+ctx}: admitted(admit(c, r, ctx), ctx, arguments(r), s)

# The oracle receives exactly the frozen configuration and received request.
# Never called before authentication; the program remains suspended.
def begin(c: S.Configuration, +s: D.State, +r: P.Request, admit: Oracle()) -> Entry:
  authenticated(c, D.authenticate(s, credential(r)), r, s, admit)

def conclude(p: Maybe<&2, N.Prepared>, s: D.State) -> Maybe<&2, N.Conclusion>:
  match p:
    case None{}: None{}
    case Some{prepared}: Some{N.conclude(prepared, s)}

def finish(t: S.Trace, c: S.Configuration, s: D.State) -> Maybe<&2, N.Conclusion>:
  match t:
    case S.Prefix{w, events}: None{}
    case S.Final{w, events, response}:
      conclude(N.prepare(N.Stopped{w, events, response}, c), s)

def early(response: S.Response, +s: D.State) -> Maybe<&2, N.Conclusion>:
  conclude(N.prepare_response(response, s, Nil{}), s)
