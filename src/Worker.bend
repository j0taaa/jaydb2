# Pure entry used literally by the generated native worker. Foreign effects
# only supply private bytes and drive Execution.advance until its terminal sum.
import Base
import ./LimitWords.bend as LimitWords
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ../contract/PreparedRegistry.bend as Registry
import ./Execution.bend as X
import ./Gate.bend as Gate
import ./Input.bend as Input
import ./Resolve.bend as Resolve
import ./Transport.bend as T
import ./ControlBridge.bend as ControlBridge
import ./Control.bend as Control
import ./Dispatch.bend as Dispatch

def entered(entry: Gate.Entry, initial: D.State) -> X.Iteration:
  match entry:
    case Gate.Halted{response}: X.result(Gate.early(response, initial))
    case Gate.Started{context, machine}: X.Continue{X.StateExecution{initial, machine}}

def selected(selection: Resolve.Selection, c: S.Configuration, +s: D.State,
  admit: Gate.Oracle()) -> X.Iteration:
  match selection:
    case Resolve.Denied{status}: X.result(Gate.early(S.response_error(status), s))
    case Resolve.Selected{r}: entered(Gate.begin(c, s, r, admit), s)

def unified(~c: S.Configuration, +s: D.State, entries: List<&2, Registry.Entry>,
  input: Resolve.Input, admit: Gate.Oracle()) -> X.Iteration:
  selected(Resolve.select(S.environment(c), s, entries, input), c, s, admit)

def decoded(~c: S.Configuration, initial: D.State, input: Input.PreAuthentication,
  admit: Gate.Oracle()) -> X.Iteration:
  match input:
    case Input.ErrorMessage{status}: X.result(Gate.early(S.response_error(status), initial))
    case Input.ErrorTransport{}: X.Inconsistent{}
    case Input.InputReady{s, r}: unified(c, s, Nil{}, Resolve.Direct{r}, admit)


def ingress(~c: S.Configuration, +s: D.State, body: List<&2, U32>,
  admit: Gate.Oracle()) -> X.Iteration:
  decoded(c, s, Input.read_message(LimitWords.convert(R.limit_message(S.limits(c)), Nat.mul(256n, 256n), B.Number64{0, 65536}, LimitWords.common_literal_exact()), body, s), admit)

def registered(~c: S.Configuration, initial: D.State, input: Input.PreAuthentication,
  entries: List<&2, Registry.Entry>, admit: Gate.Oracle()) -> X.Iteration:
  match input:
    case Input.InputReady{s, r}: unified(c, s, entries, Resolve.Registered{r}, admit)
    case other: decoded(c, initial, other, admit)

# Decode the private root once, retaining it on every early/error path.
def root(~c: S.Configuration, state: Maybe<&2, D.State>, body: List<&2, U32>,
  entries: Maybe<&2, List<&2, Registry.Entry>>, admit: Gate.Oracle()) -> X.Iteration:
  match state:
    case None{}: X.Inconsistent{}
    case Some{+s}:
      match entries:
        case None{}: ingress(c, s, body, admit)
        case Some{registry}: registered(c, s, Dispatch.execution(Dispatch.received(S.limits(c), body, s)), registry, admit)

def private_parts(~c: S.Configuration, parts: Maybe<&2, T.Parts>,
  entries: Maybe<&2, List<&2, Registry.Entry>>, admit: Gate.Oracle()) -> X.Iteration:
  match parts:
    case None{}: X.Inconsistent{}
    case Some{T.Parts{state, body}}:
      root(c, Dispatch.read_root(state, S.schema(c), S.limits(c)), body, entries, admit)

def packet(~c: S.Configuration, bytes: List<&2, U32>, admit: Gate.Oracle()) -> X.Iteration:
  private_parts(c, T.separate(bytes), None{}, admit)

# T3 forwards the latest controller registry bytes unchanged, separately from
# the handle. An absent/malformed registry supplies no execution authority.
def registry_entries(registry: Maybe<&2, Control.Registry>) -> List<&2, Registry.Entry>:
  match registry:
    case None{}: Nil{}
    case Some{r}: Control.entries(r)

# Bind the resolved tuple to the immutable artifact before its oracle can run.
def artifact_verdict(matches: Bool, c: S.Configuration, r: P.Request, ctx: D.Context,
  admit: Gate.Oracle()) -> Gate.Verdict:
  match matches:
    case False{}: Gate.ToolFailure{}
    case True{}: admit(c, r, ctx)

def artifact_oracle(+code: String, +proof: String, admit: Gate.Oracle()) -> Gate.Oracle():
  c => +r => ctx => artifact_verdict(String.eq(Gate.code(r), code) && String.eq(Resolve.proof(r), proof), c, r, ctx, admit)

def registered_packet(~c: S.Configuration, parts: Maybe<&2, T.Parts>, code: String,
  proof: String, admit: Gate.Oracle()) -> X.Iteration:
  match parts:
    case None{}: X.Inconsistent{}
    case Some{T.Parts{registry, packet}}:
      private_parts(c, T.separate(packet),
        Some{registry_entries(ControlBridge.decode_registry(registry))}, artifact_oracle(code, proof, admit))
