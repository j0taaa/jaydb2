# Pure entry used literally by the generated native worker. Foreign effects
# only supply private bytes and drive Execution.advance until its terminal sum.
import Base
import ../../../src/LimitWords.bend as LimitWords
import ../../../contract/Bytes.bend as B
import ../../../contract/Data.bend as D
import ../../../contract/Protocol.bend as P
import ../../../contract/Requirements.bend as R
import ../../../contract/Semantics.bend as S
import ../../../contract/PreparedRegistry.bend as Registry
import ../../../src/Execution.bend as X
import ../../../src/Gate.bend as Gate
import ../../../src/Input.bend as Input
import ../../../src/Resolve.bend as Resolve
import ../../../src/Transport.bend as T
import ../../../src/ControlBridge.bend as ControlBridge
import ../../../src/Control.bend as Control
import ../../../src/Dispatch.bend as Dispatch
import ../../../src/Messages.bend as Messages
import ../../../src/WorkerResult.bend as Result

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
  decoded(c, s, Input.read_message(LimitWords.convert(R.limit_message(S.limits(c))), body, s), admit)

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

# The routed entry computes the comparison once for its checked metadata and
# reuses that very Boolean at the selected request's oracle call.
def matched_oracle(matches: Bool, admit: Gate.Oracle()) -> Gate.Oracle():
  c => r => ctx => artifact_verdict(matches, c, r, ctx, admit)

def registered_packet(~c: S.Configuration, parts: Maybe<&2, T.Parts>, code: String,
  proof: String, admit: Gate.Oracle()) -> X.Iteration:
  match parts:
    case None{}: X.Inconsistent{}
    case Some{T.Parts{registry, packet}}:
      private_parts(c, T.separate(packet),
        Some{registry_entries(ControlBridge.decode_registry(registry))}, artifact_oracle(code, proof, admit))

# Routing is advisory until this checked selection and artifact comparison.
# Early denials do not depend on an artifact. A selected mismatch is returned
# before publication; the guarded oracle still prevents any client execution.
def selection_matches(selection: Resolve.Selection, code: String, proof: String) -> Bool:
  match selection:
    case Resolve.Denied{status}: True{}
    case Resolve.Selected{+r}: String.eq(Gate.code(r), code) && String.eq(Resolve.proof(r), proof)

def ready_metadata(environment: String, +s: D.State, +raw: P.Request, code: String, proof: String,
  authentication: Maybe<&2, D.Context>, selection: Resolve.Selection) -> Messages.WorkerMetadata:
  Messages.worker_metadata(environment, Some{Gate.code(raw)}, selection_matches(selection, code, proof),
    Dispatch.validated(4, Input.identity(Some{D.Context{"spoofed", "user"}}, s, raw)))

def routed_ready(~c: S.Configuration, +s: D.State, +raw: P.Request,
  entries: List<&2, Registry.Entry>, +code: String, +proof: String,
  admit: Gate.Oracle(), +authentication: Maybe<&2, D.Context>) -> Result.Iteration:
  +selection = Resolve.authenticated(authentication, S.environment(c), entries, raw)
  +metadata = ready_metadata(S.environment(c), s, raw, code, proof, authentication, selection)
  Result.attach(metadata,
    selected(selection, c, s, matched_oracle(Messages.worker_matches(metadata), admit)))

def routed_input(~c: S.Configuration, +initial: D.State, input: Input.PreAuthentication,
  entries: List<&2, Registry.Entry>, code: String, proof: String, admit: Gate.Oracle()) -> Result.Iteration:
  match input:
    case Input.InputReady{+s, +raw}:
      routed_ready(c, s, raw, entries, code, proof, admit, D.authenticate(s, Gate.credential(raw)))
    case Input.ErrorMessage{+status}:
      Result.attach(Messages.worker_metadata(S.environment(c), None{}, True{}, Input.Rejected{status}),
        decoded(c, initial, Input.ErrorMessage{status}, admit))
    case Input.ErrorTransport{}: Result.Inconsistent{}

def routed_root(~c: S.Configuration, state: Maybe<&2, D.State>, body: List<&2, U32>,
  entries: List<&2, Registry.Entry>, code: String, proof: String, admit: Gate.Oracle()) -> Result.Iteration:
  match state:
    case None{}: Result.Inconsistent{}
    case Some{+s}: routed_input(c, s, Dispatch.execution(Dispatch.received(S.limits(c), body, s)), entries, code, proof, admit)

def routed_parts(~c: S.Configuration, parts: Maybe<&2, T.Parts>,
  entries: List<&2, Registry.Entry>, code: String, proof: String, admit: Gate.Oracle()) -> Result.Iteration:
  match parts:
    case None{}: Result.Inconsistent{}
    case Some{T.Parts{state, body}}:
      routed_root(c, Dispatch.read_root(state, S.schema(c), S.limits(c)), body, entries, code, proof, admit)

# Literal prepared entry: decode the current root/registry once, authenticate
# freshly, and carry checked route/principal metadata through the native loop.
def routed_packet(~c: S.Configuration, parts: Maybe<&2, T.Parts>, code: String,
  proof: String, admit: Gate.Oracle()) -> Result.Iteration:
  match parts:
    case None{}: Result.Inconsistent{}
    case Some{T.Parts{registry, packet}}:
      routed_parts(c, T.separate(packet), registry_entries(ControlBridge.decode_registry(registry)), code, proof, admit)

def prepared_metadata(~c: S.Configuration, +s: D.State, +raw: P.Request,
  +entries: List<&2, Registry.Entry>, code: String, proof: String) -> Messages.WorkerMetadata:
  ready_metadata(S.environment(c), s, raw, code, proof, D.authenticate(s, Gate.credential(raw)),
    Resolve.select(S.environment(c), s, entries, Resolve.Registered{raw}))

law false:
  for ~c: S.Configuration
  for +s: D.State
  for +raw: P.Request
  for +entries: List<&2, Registry.Entry>
  for code: String
  for proof: String
  {Messages.worker_principal(prepared_metadata(c, s, raw, entries, code, proof)) ==
    Messages.authenticated_principal(Dispatch.validated(4, Input.authenticate_pre(Input.InputReady{s, raw}))) : Maybe<&2, String>}
def false(c, s, raw, entries, code, proof):
  match raw:
    case P.Request{credential, source, arguments, raw_proof}: {==}
