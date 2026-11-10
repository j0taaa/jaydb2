# Executable contract statements. Core/ingress/unified witnesses remain open.
# Init and independent wire witnesses are checked in proof/Init and WireTheorems.
import Base
import ./Logic.bend as L
import ./Bytes.bend as B
import ./Data.bend as D
import ./Protocol.bend as P
import ./Semantics.bend as S
import ./Requirements.bend as R
import ../src/Core.bend as N
import ../src/Execution.bend as E
import ../src/Input.bend as Input
import ../src/Request.bend as Request
import ../src/Prepared.bend as Prepared
import ../src/Transport.bend as T
import ../src/Termination.bend as Termination
import ../src/ValidationFinal.bend as ValidationFinal
import ../src/ConfigurationCheck.bend as ConfigurationCheck
import ../src/Codec.bend as C
import ../src/Gate.bend as K
import ../src/Resolve.bend as Resolve
import ./PreparedRegistry.bend as Registry

# No Environment, Happens, Processable or FailureReal argument.
def Terminates(-p: S.Program, -c: S.Configuration, -s: D.State,
  -ctx: D.Context, -args: D.Value) -> Type:
  &n: Nat -> &w: D.State -> &ts: List<&2, S.OperationEvent> -> &r: S.Response ->
    {S.execute(n, p, S.schema(c), s, ctx, args) == S.Final{w, ts, r} : S.Trace}

# A single trusted, tuple-indexed admission judgment. Source-to-program binding
# is its external interpretation, not an arbitrary Bend elaboration predicate.
def Accepted(-c: S.Configuration, -r: P.Request, -ctx: D.Context, -p: S.Program) -> Type:
  L.E<R.Certifies(c, K.code(r), p, ctx, K.arguments(r)),
    @s: D.State -> Terminates(p, c, s, ctx, K.arguments(r))>

def VerdictSound(v: K.Verdict, -c: S.Configuration, -r: P.Request,
  -ctx: D.Context) -> Type:
  match v:
    case K.Accept{p}: Accepted(c, r, ctx, p)
    case _: Unit

def OracleSoundness(-c: S.Configuration, -r: P.Request,
  -admit: K.Oracle()) -> Type:
  @ctx: D.Context -> VerdictSound(admit(c, r, ctx), c, r, ctx)

def NoFailure(r: S.Response) -> Type:
  match r:
    case S.Response{S.Failure{}, v}: Empty
    case _: Unit

def ProgramOutcome(r: S.Response) -> Type:
  match r:
    case S.Response{S.Success{}, v}: Unit
    case S.Response{S.Refusal{}, v}: Unit
    case _: Empty

# This predicate is COMPUTED from a trace, not supplied by an environment.
# Data errors are possible even for a safe terminating program.
def WithinLimits(t: S.Trace, -c: S.Configuration) -> Type:
  match t:
    case S.Prefix{w, ts}: Empty
    case S.Final{w, ts, proposal}:
      L.E<ProgramOutcome(proposal), {R.finalize(proposal, c, w) == proposal : S.Response}>

# Named clauses are shared with the causal negative controls.
def Identity(-s: D.State, -r: P.Request, -ctx: D.Context) -> Type:
  {D.authenticate(s, K.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}

def Admission(-c: S.Configuration, -r: P.Request, -admit: K.Oracle(),
  -ctx: D.Context, -p: S.Program) -> Type:
  {admit(c, r, ctx) == K.Accept{p} : K.Verdict}

def Publication(-response: S.Response, -s: D.State, -w: D.State, -next: D.State) -> Type:
  {next == S.publish(response, s, w) : D.State}

def Completion(-c: S.Configuration, -s: D.State, -w: D.State,
  -ts: List<&2, S.OperationEvent>, -proposal: S.Response) -> Type:
  &next: D.State -> &response: S.Response -> &bytes: List<&2, U32> ->
    L.E<{K.finish(S.Final{w, ts, proposal}, c, s) ==
        Some{N.Conclusion{next, response, bytes}} : Maybe<&2, N.Conclusion>},
      L.E<{response == R.finalize(proposal, c, w) : S.Response},
        L.E<Publication(response, s, w, next),
          L.E<R.Valid(c, next),
            L.E<{P.frame(S.response_value(response)) == Some{bytes} : Maybe<&2, List<&2, U32>>},
              L.E<{R.fits(R.limit_response(S.limits(c)), S.response_value(response)) == True{} : Bool},
                NoFailure(response)>>>>>>

def Finals(-c: S.Configuration, -s: D.State, -m: N.Machine) -> Type:
  @n: Nat -> @w: D.State -> @ts: List<&2, S.OperationEvent> -> @proposal: S.Response ->
    {N.traverse(n, m, S.schema(c)) == S.Final{w, ts, proposal} : S.Trace} ->
    Completion(c, s, w, ts, proposal)

def Progress(-c: S.Configuration, -s: D.State, -m: N.Machine) -> Type:
  &n: Nat -> &w: D.State -> &ts: List<&2, S.OperationEvent> -> &proposal: S.Response ->
    L.E<{N.traverse(n, m, S.schema(c)) == S.Final{w, ts, proposal} : S.Trace},
      L.E<Completion(c, s, w, ts, proposal),
        WithinLimits(S.Final{w, ts, proposal}, c) ->
          &next: D.State -> &response: S.Response -> &bytes: List<&2, U32> ->
            L.E<{K.finish(S.Final{w, ts, proposal}, c, s) ==
                Some{N.Conclusion{next, response, bytes}} : Maybe<&2, N.Conclusion>},
              ProgramOutcome(response)>>>

def Early(-c: S.Configuration, -s: D.State, -response: S.Response) -> Type:
  &bytes: List<&2, U32> ->
    L.E<{K.early(response, s) == Some{N.Conclusion{s, response, bytes}} : Maybe<&2, N.Conclusion>},
      L.E<{P.frame(S.response_value(response)) == Some{bytes} : Maybe<&2, List<&2, U32>>},
        {R.fits(R.limit_response(S.limits(c)), S.response_value(response)) == True{} : Bool}>>

def Rejection(-c: S.Configuration, -s: D.State, -r: P.Request, -admit: K.Oracle(),
  -response: S.Response) -> Type:
  {K.begin(c, s, r, admit) == K.Halted{response} : K.Entry}

# Entry is the ACTUAL result of begin, never a free event relation.
def EntryCore(entry: K.Entry, -c: S.Configuration, -s: D.State,
  -r: P.Request, -admit: K.Oracle()) -> Type:
  match entry:
    case K.Halted{response}:
      L.E<Rejection(c, s, r, admit, response), Early(c, s, response)>
    case K.Started{ctx, machine}:
      L.E<Identity(s, r, ctx),
        &p: S.Program -> L.E<Admission(c, r, admit, ctx, p),
          L.E<{machine == N.start(p, ctx, K.arguments(r), s) : N.Machine},
            L.E<Accepted(c, r, ctx, p),
              L.E<(@n: Nat -> R.SafetyTrace(N.traverse(n, machine, S.schema(c)),
                c, s, ctx, K.code(r), K.arguments(r))),
                L.E<Finals(c, s, machine), Progress(c, s, machine)>>>>>>

def Core(c: S.Configuration, s: D.State, r: P.Request,
  admit: K.Oracle()) -> Type:
  EntryCore(K.begin(c, s, r, admit), c, s, r, admit)

def CoreTheorem() -> Type:
  @c: S.Configuration -> @s: D.State -> @r: P.Request ->
    @admit: (K.Oracle()) ->
      {R.configuration_is_valid(c) == True{} : Bool} -> R.Valid(c, s) ->
        OracleSoundness(c, r, admit) -> Core(c, s, r, admit)

# Init is typed admission of a seed proof, not a Boolean runtime law test.
type SeedVerdict<-c: S.Configuration, -seed: D.State> is Type:
  SeedReject{}
  SeedAccept{valid: R.Valid(c, seed)}

def start_seed(-c: S.Configuration, -seed: D.State, ok: Bool, v: SeedVerdict<c, seed>, value: D.State) -> Maybe<&2, D.State>:
  match ok v:
    case True{} SeedAccept{valid}: Some{value}
    case _ _: None{}

def init(c: S.Configuration, +seed: D.State, v: SeedVerdict<c, seed>) -> Maybe<&2, D.State>:
  start_seed(c, seed, R.configuration_is_valid(c), v, seed)

def SeedAccepted(-c: S.Configuration, -seed: D.State, v: SeedVerdict<c, seed>) -> Type:
  match v:
    case SeedAccept{valid}: Unit
    case SeedReject{}: Empty

def InitAt(-c: S.Configuration, -seed: D.State, -v: SeedVerdict<c, seed>, -ok: Bool) -> Type:
  L.E<(@started: D.State -> {start_seed(c, seed, ok, v, seed) == Some{started} : Maybe<&2, D.State>} ->
      L.E<{started == seed : D.State},
        L.E<{ok == True{} : Bool}, R.Valid(c, started)>>),
    L.E<({ok == True{} : Bool} -> SeedAccepted(c, seed, v) ->
      {start_seed(c, seed, ok, v, seed) == Some{seed} : Maybe<&2, D.State>}),
      {start_seed(c, seed, ok, SeedReject{}, seed) == None{} : Maybe<&2, D.State>}>>

def Init(-c: S.Configuration, -seed: D.State, -v: SeedVerdict<c, seed>) -> Type:
  InitAt(c, seed, v, R.configuration_is_valid(c))

def InitTheorem() -> Type:
  @c: S.Configuration -> @seed: D.State -> @v: SeedVerdict<c, seed> -> Init(c, seed, v)

# Public encoding uses P.encode; the executable decoder is C.decode.
def CodecRoundtrip() -> Type:
  @v: D.Value -> @bytes: List<&2, U32> -> @body: B.Number64 -> @ceiling: B.Number64 ->
    {P.encode(v) == Some{bytes} : Maybe<&2, List<&2, U32>>} ->
    {B.nat64(B.length(bytes)) == Some{body} : Maybe<&2, B.Number64>} ->
    {C.less_equal64(body, ceiling) == True{} : Bool} ->
    {C.decode(bytes, ceiling) == C.Decoded{v} : C.Outcome}

def CodecCanonical() -> Type:
  @bytes: List<&2, U32> -> @ceiling: B.Number64 -> @v: D.Value ->
    {C.decode(bytes, ceiling) == C.Decoded{v} : C.Outcome} ->
    {P.encode(v) == Some{bytes} : Maybe<&2, List<&2, U32>>}

def FramingRoundtrip() -> Type:
  @first: List<&2, U32> -> @second: List<&2, U32> -> @packet: List<&2, U32> ->
    {B.octets_all_valid(first) == True{} : Bool} ->
    {B.octets_all_valid(second) == True{} : Bool} ->
    {T.join(first, second) == Some{packet} : Maybe<&2, List<&2, U32>>} ->
    {T.separate(packet) == Some{T.Parts{first, second}} : Maybe<&2, T.Parts>}

# The execution invariant is shared after checked prepared normalization.
# The concrete select function is in Resolve.bend; no free lookup predicate.
def SelectedCore(selection: Resolve.Selection, c: S.Configuration, s: D.State,
  admit: K.Oracle()) -> Type:
  match selection:
    case Resolve.Denied{status}: Early(c, s, S.response_error(status))
    case Resolve.Selected{r}: Core(c, s, r, admit)

def UnifiedCore(c: S.Configuration, +s: D.State,
  entries: List<&2, Registry.Entry>, input: Resolve.Input, admit: K.Oracle()) -> Type:
  match c:
    case S.Configuration{schema, laws, limits, +environment}:
      SelectedCore(Resolve.select(environment, s, entries, input),
        S.Configuration{schema, laws, limits, environment}, s, admit)

def SelectedOracleSoundness(selection: Resolve.Selection, -c: S.Configuration,
  -admit: K.Oracle()) -> Type:
  match selection:
    case Resolve.Denied{status}: Unit
    case Resolve.Selected{r}: OracleSoundness(c, r, admit)

def ResolvedOracleSoundness(c: S.Configuration, s: D.State,
  entries: List<&2, Registry.Entry>, input: Resolve.Input, -admit: K.Oracle()) -> Type:
  SelectedOracleSoundness(Resolve.select(S.environment(c), s, entries, input), c, admit)

def UnifiedCoreTheorem() -> Type:
  @c: S.Configuration -> @s: D.State -> @entries: List<&2, Registry.Entry> ->
    @input: Resolve.Input -> @admit: K.Oracle() ->
      {R.configuration_is_valid(c) == True{} : Bool} -> R.Valid(c, s) ->
        ResolvedOracleSoundness(c, s, entries, input, admit) ->
          UnifiedCore(c, s, entries, input, admit)

# Ordinary complete-body ingress. Header receipt policy is a separate adapter.
def DecodedCore(input: Input.PreAuthentication, c: S.Configuration,
  s: D.State, admit: K.Oracle()) -> Type:
  match input:
    case Input.ErrorMessage{status}: Early(c, s, S.response_error(status))
    case Input.ErrorTransport{}: Empty
    case Input.InputReady{state, r}: L.E<{state == s : D.State}, Core(c, s, r, admit)>

def IngressCore(c: S.Configuration, +s: D.State,
  body: List<&2, U32>, admit: K.Oracle()) -> Type:
  match c:
    case S.Configuration{schema, laws, +limits, environment}:
      DecodedCore(Input.read_message(B.nat64(R.limit_message(limits)), body, s),
        S.Configuration{schema, laws, limits, environment}, s, admit)

def DecodedOracleSoundness(input: Input.PreAuthentication, -c: S.Configuration,
  -admit: K.Oracle()) -> Type:
  match input:
    case Input.InputReady{state, r}: OracleSoundness(c, r, admit)
    case _: Unit

def IngressOracleSoundness(c: S.Configuration, s: D.State,
  body: List<&2, U32>, -admit: K.Oracle()) -> Type:
  DecodedOracleSoundness(Input.read_message(B.nat64(R.limit_message(S.limits(c))), body, s), c, admit)

def IngressTheorem() -> Type:
  @c: S.Configuration -> @s: D.State -> @body: List<&2, U32> -> @admit: K.Oracle() ->
    {R.configuration_is_valid(c) == True{} : Bool} -> R.Valid(c, s) ->
      IngressOracleSoundness(c, s, body, admit) -> IngressCore(c, s, body, admit)
