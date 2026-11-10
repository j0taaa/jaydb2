# Executable contract statements over the actual gate, interpreter and finisher.
# Witnesses: proof/Init (Init), proof/CoreClauses (Core), proof/Ingress
# (Ingress, UnifiedCore), proof/Iteration (Fold), proof/WireTheorems (wire).
import Base
import ../src/Control.bend as Control
import ../src/Dispatch.bend as Dispatch
import ./PreparedProtocol.bend as PreparedProtocol
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

# Every installed law holds at prefix n of the actual machine.
def Safety(c: S.Configuration, -s: D.State, -r: P.Request, -ctx: D.Context,
  m: N.Machine, n: Nat) -> Type:
  R.SafetyTrace(N.traverse(n, m, S.schema(c)), c, s, ctx, K.code(r), K.arguments(r))

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

# The four clauses of the core contract. Each clause is proved separately
# under identical universal premises; CoreTheorem quantifies over all four,
# so it is exactly their conjunction. Identity/admission pin the machine
# that the other clauses describe: all four inspect the same computed entry.
type Clause is Data:
  Admitted{}
  Safe{}
  Completed{}
  Progressing{}

# Entry is the ACTUAL result of begin, never a free event relation.
def EntryCore(k: Clause, entry: K.Entry, -c: S.Configuration, -s: D.State,
  -r: P.Request, -admit: K.Oracle()) -> Type:
  match k entry:
    case Admitted{} K.Halted{response}:
      L.E<Rejection(c, s, r, admit, response), Early(c, s, response)>
    case Admitted{} K.Started{ctx, machine}:
      L.E<Identity(s, r, ctx),
        &p: S.Program -> L.E<Admission(c, r, admit, ctx, p),
          {machine == N.start(p, ctx, K.arguments(r), s) : N.Machine}>>
    case Safe{} K.Halted{response}: Unit
    case Safe{} K.Started{ctx, machine}: @n: Nat -> Safety(c, s, r, ctx, machine, n)
    case Completed{} K.Halted{response}: Unit
    case Completed{} K.Started{ctx, machine}: Finals(c, s, machine)
    case Progressing{} K.Halted{response}: Unit
    case Progressing{} K.Started{ctx, machine}: Progress(c, s, machine)

def Core(k: Clause, c: S.Configuration, s: D.State, r: P.Request,
  admit: K.Oracle()) -> Type:
  EntryCore(k, K.begin(c, s, r, admit), c, s, r, admit)

def CoreClauseTheorem(k: Clause) -> Type:
  @c: S.Configuration -> @s: D.State -> @r: P.Request ->
    @admit: (K.Oracle()) ->
      {R.configuration_is_valid(c) == True{} : Bool} -> R.Valid(c, s) ->
        OracleSoundness(c, r, admit) -> Core(k, c, s, r, admit)

def CoreTheorem() -> Type:
  @k: Clause -> CoreClauseTheorem(k)

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

# Fixed denial before execution. Its bounded response belongs to the
# admission clause, matching a halted gate in EntryCore.
def Denial(k: Clause, -c: S.Configuration, -s: D.State, -response: S.Response) -> Type:
  match k:
    case Admitted{}: Early(c, s, response)
    case _: Unit

# The execution invariant is shared after checked prepared normalization.
# The concrete select function is in Resolve.bend; no free lookup predicate.
def SelectedCore(k: Clause, selection: Resolve.Selection, c: S.Configuration, s: D.State,
  admit: K.Oracle()) -> Type:
  match selection:
    case Resolve.Denied{status}: Denial(k, c, s, S.response_error(status))
    case Resolve.Selected{r}: Core(k, c, s, r, admit)

def UnifiedCore(k: Clause, c: S.Configuration, +s: D.State,
  entries: List<&2, Registry.Entry>, input: Resolve.Input, admit: K.Oracle()) -> Type:
  match c:
    case S.Configuration{schema, laws, limits, +environment}:
      SelectedCore(k, Resolve.select(environment, s, entries, input),
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
  @k: Clause -> @c: S.Configuration -> @s: D.State -> @entries: List<&2, Registry.Entry> ->
    @input: Resolve.Input -> @admit: K.Oracle() ->
      {R.configuration_is_valid(c) == True{} : Bool} -> R.Valid(c, s) ->
        ResolvedOracleSoundness(c, s, entries, input, admit) ->
          UnifiedCore(k, c, s, entries, input, admit)

# Ordinary complete-body ingress. Header receipt policy is a separate adapter.
def DecodedCore(k: Clause, input: Input.PreAuthentication, c: S.Configuration,
  s: D.State, admit: K.Oracle()) -> Type:
  match input:
    case Input.ErrorMessage{status}: Denial(k, c, s, S.response_error(status))
    case Input.ErrorTransport{}: Empty
    case Input.InputReady{state, r}: L.E<{state == s : D.State}, Core(k, c, s, r, admit)>

def IngressCore(k: Clause, c: S.Configuration, +s: D.State,
  body: List<&2, U32>, admit: K.Oracle()) -> Type:
  match c:
    case S.Configuration{schema, laws, +limits, environment}:
      DecodedCore(k, Input.read_message(B.nat64(R.limit_message(limits)), body, s),
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
  @k: Clause -> @c: S.Configuration -> @s: D.State -> @body: List<&2, U32> -> @admit: K.Oracle() ->
    {R.configuration_is_valid(c) == True{} : Bool} -> R.Valid(c, s) ->
      IngressOracleSoundness(c, s, body, admit) -> IngressCore(k, c, s, body, admit)

# Finite serial runs. Each step is the computed result of the actual gate,
# interpreter and finisher, and the host feeds exactly the returned root into
# the next step (Gate.accepted_begin turns StepRan's two equations into begin's
# Started result). No validity of any reached state is assumed.
type Step<-c: S.Configuration, -s: D.State, -r: P.Request, -admit: K.Oracle(), -next: D.State> is Type:
  StepHalted{response: S.Response, bytes: List<&2, U32>,
    halted: {K.begin(c, s, r, admit) == K.Halted{response} : K.Entry},
    published: {K.early(response, s) == Some{N.Conclusion{next, response, bytes}} : Maybe<&2, N.Conclusion>}}
  StepRan{context: D.Context, program: S.Program, n: Nat, w: D.State,
    ts: List<&2, S.OperationEvent>, proposal: S.Response, response: S.Response, bytes: List<&2, U32>,
    authenticated: {D.authenticate(s, K.credential(r)) == Some{context} : Maybe<&2, D.Context>},
    admitted: {admit(c, r, context) == K.Accept{program} : K.Verdict},
    finished: {N.traverse(n, N.start(program, context, K.arguments(r), s), S.schema(c)) ==
      S.Final{w, ts, proposal} : S.Trace},
    published: {K.finish(S.Final{w, ts, proposal}, c, s) ==
      Some{N.Conclusion{next, response, bytes}} : Maybe<&2, N.Conclusion>}}

# A finite input sequence from root s, each step with a sound oracle.
type Run<-c: S.Configuration, -s: D.State> is Type:
  RunEnd{}
  RunStep{request: P.Request, admit: K.Oracle(), next: D.State,
    sound: OracleSoundness(c, request, admit),
    step: Step<c, s, request, admit, next>,
    rest: Run<c, next>}

# Core clause k at step j of the run (nothing past its end).
def CoreAt(j: Nat, k: Clause, c: S.Configuration, s: D.State, run: Run<c, s>) -> Type:
  match j run:
    case _ RunEnd{}: Unit
    case 0n RunStep{r, admit, next, sound, step, rest}: Core(k, c, s, r, admit)
    case 1n+i RunStep{r, admit, next, sound, step, rest}: CoreAt(i, k, c, next, rest)

# Validity of the root before step j, or of the final root past the end.
def ValidAt(j: Nat, -c: S.Configuration, -s: D.State, run: Run<c, s>) -> Type:
  match j run:
    case _ RunEnd{}: R.Valid(c, s)
    case 0n RunStep{r, admit, next, sound, step, rest}: R.Valid(c, s)
    case 1n+i RunStep{r, admit, next, sound, step, rest}: ValidAt(i, c, next, rest)

# FoldTheorem quantifies over every step index j and every aspect: each Core
# clause at step j, and validity of every reached root.
type Aspect is Data:
  StepCore{clause: Clause}
  Reached{}

def FoldAt(a: Aspect, c: S.Configuration, s: D.State, run: Run<c, s>, j: Nat) -> Type:
  match a:
    case StepCore{k}: CoreAt(j, k, c, s, run)
    case Reached{}: ValidAt(j, c, s, run)

def FoldTheorem() -> Type:
  @a: Aspect -> @c: S.Configuration -> @seed: D.State -> @v: SeedVerdict<c, seed> ->
    @run: Run<c, seed> -> {init(c, seed, v) == Some{seed} : Maybe<&2, D.State>} ->
      @j: Nat -> FoldAt(a, c, seed, run, j)

# Prepared control commands supplement, and do not weaken, the transaction
# statements above. Admission tokens are T1's exact universal acceptance tuple.

type ControlClause is Data:
  ControlPreserved{}
  ControlDelta{}
  ControlChecked{}
  ControlReception{}

def ControlIdentity(-s: D.State, -r: P.Request, -ctx: D.Context) -> Type:
  {D.authenticate(s, K.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}

def ControlChangeAtBounds(prepare: Bool, invalidate: Bool, -limits: S.Limits, -instance: String, -registry: Control.Registry,
  -r: P.Request, -a: Control.Admission, -h: String,
  -change: Control.Change, -receipt: PreparedProtocol.Receipt) -> Type:
  match prepare invalidate:
    case True{} _:
      L.E<{Control.admission_matches(a, instance, r) == True{} : Bool},
        L.E<{Control.candidate_valid(h) == True{} : Bool},
          L.E<{Control.member(h, Control.allocated(registry)) == False{} : Bool},
            L.E<{change == Control.ControlAdd{Registry.Entry{instance, h,
              K.code(r), Resolve.proof(r), False{}, ""}} : Control.Change},
              {receipt == PreparedProtocol.PreparedReceipt{h} : PreparedProtocol.Receipt}>>>>
    case False{} True{}:
      L.E<{String.eq(Resolve.proof(r), "") == True{} : Bool},
        L.E<(&entry: Registry.Entry ->
          {Registry.lookup(instance, K.code(r), Control.entries(registry)) == Some{entry} : Maybe<&2, Registry.Entry>}),
          L.E<{change == Control.ControlRemove{instance, K.code(r)} : Control.Change},
            {receipt == PreparedProtocol.InvalidatedReceipt{} : PreparedProtocol.Receipt}>>>
    case False{} False{}: Empty

def ControlChangeAt(prepare: Bool, invalidate: Bool, -c: S.Configuration, -registry: Control.Registry,
  -r: P.Request, -a: Control.Admission, -h: String, -change: Control.Change, -receipt: PreparedProtocol.Receipt) -> Type:
  ControlChangeAtBounds(prepare, invalidate, S.limits(c), S.environment(c), registry, r, a, h, change, receipt)

def ControlChange(+tag: U32, -c: S.Configuration, -registry: Control.Registry,
  -r: P.Request, -a: Control.Admission, -h: String, -change: Control.Change, -receipt: PreparedProtocol.Receipt) -> Type:
  ControlChangeAt(U32.is_eq(tag, 3), U32.is_eq(tag, 5), c, registry, r, a, h, change, receipt)

def ControlReceipt(-c: S.Configuration, -receipt: PreparedProtocol.Receipt,
  -bytes: List<&2, U32>) -> Type:
  L.E<{PreparedProtocol.frame_receipt(receipt) == Some{bytes} : Maybe<&2, List<&2, U32>>},
    {R.fits(R.limit_response(S.limits(c)), PreparedProtocol.receipt_value(receipt)) == True{} : Bool}>

def ControlPlanAtBounds(plan: Control.Plan, -limits: S.Limits, -instance: String, -s: D.State, -r: P.Request,
  -prepare: Bool, -invalidate: Bool, -registry: Control.Registry, -a: Control.Admission, -h: String) -> Type:
  match plan:
    case Control.ControlDenied{status}: Unit
    case Control.ControlReady{ctx, change, receipt, bytes}:
      L.E<ControlIdentity(s, r, ctx),
        L.E<ControlChangeAt(prepare, invalidate, S.Configuration{D.Schema{Nil{}}, S.NoneLaw{}, limits, instance}, registry, r, a, h, change, receipt), ControlReceipt(S.Configuration{D.Schema{Nil{}}, S.NoneLaw{}, limits, instance}, receipt, bytes)>>

def ControlPlanAt(plan: Control.Plan, -c: S.Configuration, -s: D.State, -r: P.Request,
  -prepare: Bool, -invalidate: Bool, -registry: Control.Registry, -a: Control.Admission, -h: String) -> Type:
  ControlPlanAtBounds(plan, S.limits(c), S.environment(c), s, r, prepare, invalidate, registry, a, h)

def ControlErrors(plan: Control.Plan) -> Type:
  match plan:
    case Control.ControlDenied{status}: Unit
    case _: Empty

def ControlPlanBounds(plan: Control.Plan, routed: Dispatch.Routed, -limits: S.Limits, -instance: String,
  -registry: Control.Registry, -a: Control.Admission, -h: String) -> Type:
  match routed:
    case Dispatch.Routed{tag, Input.InputReady{s, r}}:
      ControlPlanAt(plan, S.Configuration{D.Schema{Nil{}}, S.NoneLaw{}, limits, instance}, s, r, U32.is_eq(tag, 3), U32.is_eq(tag, 5), registry, a, h)
    case _: ControlErrors(plan)

def ControlPlan(plan: Control.Plan, routed: Dispatch.Routed, -c: S.Configuration,
  -registry: Control.Registry, -a: Control.Admission, -h: String) -> Type:
  ControlPlanBounds(plan, routed, S.limits(c), S.environment(c), registry, a, h)

def ControlRooted(routed: Dispatch.Routed, -root: D.State) -> Type:
  match routed:
    case Dispatch.Routed{tag, Input.InputReady{s, r}}: {s == root : D.State}
    case _: Unit

def ControlMeasuredLimit(plan: Control.Plan, -limit: Nat, -body: List<&2, U32>) -> Type:
  match plan:
    case Control.ControlDenied{status}: Unit
    case _: {Nat.is_le(B.length(body), limit) == True{} : Bool}

def ControlMeasured(plan: Control.Plan, -c: S.Configuration, -body: List<&2, U32>) -> Type:
  ControlMeasuredLimit(plan, R.limit_message(S.limits(c)), body)

def ControlDeltaFor(plan: Control.Plan, -registry: Control.Registry, -reg: Control.Registry, -outcome: Control.Outcome) -> Type:
  match plan:
    case Control.ControlDenied{status}:
      L.E<{reg == registry : Control.Registry},
        {outcome == Control.ControlTransaction{S.response_error(status)} : Control.Outcome}>
    case Control.ControlReady{ctx, change, receipt, bytes}:
      L.E<{reg == Control.apply(change, registry) : Control.Registry},
        {outcome == Control.ControlMetadata{receipt, bytes, change} : Control.Outcome}>

def ControlPreservedResult(-root: D.State, -last: List<&2, U32>, result: Control.Transition) -> Type:
  match result:
    case Control.ControlResult{next, paired, reg, outcome}:
      L.E<{next == root : D.State}, {paired == last : List<&2, U32>}>

def ControlDeltaResult(plan: Control.Plan, -registry: Control.Registry, result: Control.Transition) -> Type:
  match result:
    case Control.ControlResult{next, paired, reg, outcome}: ControlDeltaFor(plan, registry, reg, outcome)

def ControlResult(k: ControlClause, plan: Control.Plan, c: S.Configuration,
  root: D.State, last: List<&2, U32>, registry: Control.Registry,
  body: List<&2, U32>, a: Control.Admission, h: String, result: Control.Transition) -> Type:
  match k:
    case ControlPreserved{}: ControlPreservedResult(root, last, result)
    case ControlDelta{}: ControlDeltaResult(plan, registry, result)
    case ControlChecked{}: ControlPlan(plan, Dispatch.received(S.limits(c), body, root), c, registry, a, h)
    case ControlReception{}:
      L.E<ControlRooted(Dispatch.received(S.limits(c), body, root), root), ControlMeasured(plan, c, body)>

# Control policy uses limits and instance only. Normalize unused schema/law
# fields in its predicates so affine configuration functions are consumed once.
# ControlAdmissionSound below retains the ORIGINAL full configuration.
def ControlAtPlan(+plan: Control.Plan, k: ControlClause, +schema: D.Schema, +limits: S.Limits, +instance: String,
  +root: D.State, +last: List<&2, U32>, +registry: Control.Registry, +body: List<&2, U32>,
  +a: Control.Admission, +h: String) -> Type:
  ControlResult(k, plan, S.Configuration{schema, S.NoneLaw{}, limits, instance}, root, last, registry, body, a, h,
    Control.finish(plan, root, last, registry))

def ControlAt(c: S.Configuration, k: ControlClause, +root: D.State,
  +last: List<&2, U32>, +registry: Control.Registry, +body: List<&2, U32>,
  +a: Control.Admission, +h: String) -> Type:
  match c:
    case S.Configuration{+schema, laws, +limits, +instance}:
      ControlAtPlan(Control.plan(S.Configuration{schema, laws, limits, instance}, root, registry, body, a, h),
        k, schema, limits, instance, root, last, registry, body, a, h)

# T1's judgment is indexed by the exact admitted source, proof and instance.
# The proof-source/Book binding is the same external interpretation as Accepted.
def ControlAdmissionSound(-c: S.Configuration, a: Control.Admission) -> Type:
  match a:
    case Control.ControlUnaccepted{}: Unit
    case Control.ControlUniversal{instance, code, proof}:
      &program: S.Program ->
        L.E<(@ctx: D.Context -> @args: D.Value -> R.Certifies(c, code, program, ctx, args)),
          (@state: D.State -> @ctx: D.Context -> @args: D.Value -> Terminates(program, c, state, ctx, args))>

def ControlTheorem() -> Type:
  @k: ControlClause -> @c: S.Configuration -> @root: D.State -> @last: List<&2, U32> ->
    @registry: Control.Registry -> @body: List<&2, U32> -> @a: Control.Admission -> @h: String ->
      ControlAdmissionSound(c, a) -> ControlAt(c, k, root, last, registry, body, a, h)
