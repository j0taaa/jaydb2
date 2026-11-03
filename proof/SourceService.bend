# Protocol origin and environment. JudgmentSyntactic is syntax, not a Boolean checker.
# elaborates/derives families are official-system relations; soundness and
# refinement are separate contracts. This module grants no Law1..Law8.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/Resources.bend as X
import ../contract/Semantics.bend as S
import ./ProtocolService.bend as Q
import ./RoutesService.bend as R
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as Req
import ../src/Core.bend as N
import ./ExecutionService.bend as Exec
import ../contract/Bytes.bend as B
import ../src/Input.bend as E
import ./InputRelations.bend as Messages
import ./PhasesService.bend as Phases
import ../src/ConfigurationCheck.bend as Config
import ../src/Transport.bend as T
import ./Transport.bend as Transport
import ./Foundations.bend as F

type FileSource is Data:
  FileSource{path: String, content: String}

# Denotes the term declared in these closed modules. Being supplied is no
# derivability proof: that belongs to the official logical relation, never the Accepted bit.
type JudgmentSyntactic is Data:
  JudgmentSyntactic{modules: List<&2, FileSource>, input: String, declaration: String}

# The seed participates only in initialization/metatheory, not in the client's Book.
type InitialData is Data:
  InitialData{configuration_source: JudgmentSyntactic, state_source: JudgmentSyntactic,
    proof_source: JudgmentSyntactic, judgment: R.Judgment, result: R.ResultInitial, micro: R.Micro}

type CallData is Data:
  CallData{configuration_source: JudgmentSyntactic, program_source: JudgmentSyntactic,
    certificate_source: JudgmentSyntactic, terminates_source: JudgmentSyntactic,
    state: List<&2, U32>, tools: R.DataTools, micro: R.Micro}

# Query context is data; the closed configuration is not copied.
type Context is Data:
  Initial{world: Nat, state: D.State, proof: String}
  Service{world: Nat, state: D.State, input: X.Reception}

def scenario_context(~c: S.Configuration, x: Context) -> I.Scenario:
  match x:
    case Initial{m, s, pi}: I.Initialize{m, c, s, pi}
    case Service{m, s, r}: I.Serve{m, c, s, r}

def RequestOfPhase(~c: S.Configuration, +x: Context, phase: R.PhaseBefore) -> Type:
  match phase:
    case R.BeforeInput{}: Unit
    case R.AfterReceive{r}: I.RequestReceived(scenario_context(c, x), r)
    case R.AfterAuthenticate{r, ctx}: I.RequestReceived(scenario_context(c, x), r)
    case R.AfterVerify{r, ctx}: I.RequestReceived(scenario_context(c, x), r)
    case R.Executing{r, ctx, qs}: I.RequestReceived(scenario_context(c, x), r)
    case R.AfterPrepare{r, ctx, qs, p}: I.RequestReceived(scenario_context(c, x), r)

def RequestOfBranch(~c: S.Configuration, +x: Context, branch: R.Branch) -> Type:
  match branch:
    case R.AutRefusal{r, delivery}: I.RequestReceived(scenario_context(c, x), r)
    case R.GateRefusal{r, ctx, delivery}: I.RequestReceived(scenario_context(c, x), r)
    case R.Executed{r, ctx, qs, p, delivery}: I.RequestReceived(scenario_context(c, x), r)
    case R.FatalAfterPublication{r, ctx, qs, p, stage, id}: I.RequestReceived(scenario_context(c, x), r)
    case R.FailureBefore{phase, stage, id, fatal, delivery}: RequestOfPhase(c, x, phase)
    case R.Pending{phase}: RequestOfPhase(c, x, phase)
    case _: Unit

type ObservationData is Data:
  ObservationData{initial: Maybe<&2, D.State>, frames: List<&2, Q.Frame>,
    program_source: Maybe<&2, JudgmentSyntactic>}

def construct_initial(~identity: String, c: S.Configuration, +s: D.State, data: InitialData) -> ObservationData:
  match data:
    case InitialData{cf, sf, pf, judgment, result, micro}:
      ObservationData{None{}, R.generate_result_initial(c, identity, s, judgment, result, micro), None{}}

def construct_call(c: S.Configuration, +s: D.State, reception: X.Reception,
  data: CallData) -> ObservationData:
  match data:
    case CallData{cf, program, certificate, terminates, state, tools, micro}:
      ObservationData{Some{s}, R.generate(c, reception, state, s, tools, micro), Some{program}}

# Inert index: the Initialize branch has no client program.
# It is neither an offered transaction nor an admission fallback.
def without_program() -> S.Program:
  S.Program{ctx => args => S.Refuse{D.VAbsent{}}}

# A closed reproducible source. Logical contracts are not checker
# Booleans. No field grants a database law or post-publication validity.
type Source is Type:
  Source{identity: String, artifact: String, scenarios: Nat -> I.Scenario,
    initial: Nat -> InitialData, calls: Nat -> CallData,
    program: JudgmentSyntactic -> S.Program,
    elaborates: S.Configuration -> String -> S.Program -> Type,
    derives: S.Configuration -> String -> Type -> Type,
    processable: I.Scenario -> Type,
    failure: String -> I.Scenario -> Nat -> X.Stage -> String -> Bool -> Type,
    delivery_failed: String -> I.Scenario -> Nat -> Type}

def identity(f: Source) -> String:
  Source{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  id

def artifact(f: Source) -> String:
  Source{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  k

def scenario(f: Source, world: Nat) -> I.Scenario:
  Source{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  cs(world)

def initial(f: Source, world: Nat) -> InitialData:
  Source{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  ins(world)

def call(f: Source, world: Nat) -> CallData:
  Source{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  hs(world)

def program(f: Source, source: JudgmentSyntactic) -> S.Program:
  Source{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  ps(source)

def of_origin(~source: Source, -c: S.Configuration,
  initial: Maybe<&2, D.State>, frames: List<&2, Q.Frame>,
  origin: Maybe<&2, JudgmentSyntactic>, t: Nat, f: I.Fact) -> Type:
  match origin:
    case None{}: Q.observes_service(c, without_program(), initial, frames, t, f)
    case Some{origin}: Q.observes_service(c, program(source, origin), initial, frames, t, f)

def of_observation(~source: Source, -c: S.Configuration,
  data: ObservationData, t: Nat, f: I.Fact) -> Type:
  match data:
    case ObservationData{initial, frames, origin}: of_origin(source, c, initial, frames, origin, t, f)

# One route per world: x merely proves it describes that actual
# scenario. Generation always queries the canonical scenario, never x again.
def of_route(~source: Source, x: I.Scenario, t: Nat, f: I.Fact) -> Type:
  match x:
    case I.Initialize{+world, c, +s, pi}:
      of_observation(source, c, construct_initial(identity(source), c, s, initial(source, world)), t, f)
    case I.Serve{+world, c, +s, reception}:
      of_observation(source, c, construct_call(c, s, reception, call(source, world)), t, f)

def world(x: I.Scenario) -> Nat:
  match x:
    case I.Initialize{m, c, s, pi}: m
    case I.Serve{m, c, s, r}: m

def observe_source(~source: Source, x: I.Scenario, t: Nat, f: I.Fact) -> Type:
  match x:
    case I.Initialize{+world, c, +s, pi}:
      L.E<{I.Initialize{world, c, s, pi} == scenario(source, world) : I.Scenario},
        of_route(source, scenario(source, world), t, f)>
    case I.Serve{+world, c, +s, reception}:
      L.E<{I.Serve{world, c, s, reception} == scenario(source, world) : I.Scenario},
        of_route(source, scenario(source, world), t, f)>

# These are only two directions of the same J, not two observers.
def origin_literal_divided(~source: Source, -x: I.Scenario, -y: I.Scenario, -t: Nat, -f: I.Fact,
  equal: L.E<{x == y : I.Scenario}, {x == y : I.Scenario}>, obs: of_route(source, y, t, f)) ->
  L.E<{x == y : I.Scenario}, of_route(source, x, t, f)>:
  match equal:
    case L.Both{guard, substitution}:
      L.Both{guard, (%Equal.sym(I.Scenario, x, y, substitution) : of_route(source, _, t, f) obs)}

def origin_literal(~source: Source, -x: I.Scenario, -y: I.Scenario, -t: Nat, -f: I.Fact,
  equal: {x == y : I.Scenario}, obs: of_route(source, y, t, f)) ->
  L.E<{x == y : I.Scenario}, of_route(source, x, t, f)>:
  origin_literal_divided(source, x, y, t, f, Q.equality_reopenable(I.Scenario, x, y, equal), obs)

def origin_canonical(~source: Source, -x: I.Scenario, -y: I.Scenario, -t: Nat, -f: I.Fact,
  equal: {x == y : I.Scenario}, obs: of_route(source, x, t, f)) ->
  L.E<{x == y : I.Scenario}, of_route(source, y, t, f)>:
  %equal : L.E<{x == _ : I.Scenario}, of_route(source, _, t, f)>
  L.Both{{==}, obs}

def elaboration(f: Source, c: S.Configuration, code: String, p: S.Program) -> Type:
  Source{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  el(c, code, p)

def derivation(f: Source, c: S.Configuration, text: String, target: Type) -> Type:
  Source{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  de(c, text, target)

def processable(f: Source, x: I.Scenario) -> Type:
  Source{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  pr(x)

def failure(f: Source, code: String, x: I.Scenario, t: Nat,
  stage: X.Stage, name: String, fatal: Bool) -> Type:
  Source{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  fr(code, x, t, stage, name, fatal)

def failure_delivery(f: Source, code: String, x: I.Scenario, t: Nat) -> Type:
  Source{id, k, cs, ins, hs, ps, el, de, pr, fr, ef} = f
  ef(code, x, t)

def environment(~source: Source) -> I.Environment:
  I.Environment{identity(source),
    c => code => p => elaboration(source, c, code, p),
    c => text => target => derivation(source, c, text, target),
    code => x => t => f => L.E<{code == artifact(source) : String},
      observe_source(source, x, t, f)>, x => processable(source, x),
    code => x => t => stage => name => fatal => failure(source, code, x, t, stage, name, fatal),
    code => x => t => failure_delivery(source, code, x, t)}

# Introduce/eliminate the artifact guard. Remaining content preserves
# equality with the canonical scenario and the actually generated route query.
def eliminate_fact(~source: Source, -k: String, -x: I.Scenario, -t: Nat, -f: I.Fact,
  fact: I.Happens(environment(source), k, x, t, f)) ->
  L.E<{k == artifact(source) : String}, observe_source(source, x, t, f)>:
  fact

def introduce_fact(~source: Source, -k: String, -x: I.Scenario, -t: Nat, -f: I.Fact,
  name: {k == artifact(source) : String}, obs: observe_source(source, x, t, f)) ->
  I.Happens(environment(source), k, x, t, f):
  L.Both{name, obs}

def fact_literal_of_world(~source: Source, -k: String, -x: I.Scenario, -m: Nat,
  -t: Nat, -f: I.Fact, input: L.E<{k == artifact(source) : String},
    L.E<{x == scenario(source, m) : I.Scenario}, of_route(source, scenario(source, m), t, f)>>) ->
  L.E<{k == artifact(source) : String}, L.E<{x == scenario(source, m) : I.Scenario}, of_route(source, x, t, f)>>:
  match input:
    case L.Both{name, L.Both{equal, obs}}:
      L.Both{name, origin_literal(source, x, scenario(source, m), t, f, equal, obs)}

def eliminate_fact_literal(~source: Source, -k: String, x: I.Scenario, -t: Nat, -f: I.Fact,
  fact: I.Happens(environment(source), k, x, t, f)) ->
  L.E<{k == artifact(source) : String},
    L.E<{x == scenario(source, world(x)) : I.Scenario}, of_route(source, x, t, f)>>:
  match x:
    case I.Initialize{+m, c, +s, +pi}: fact_literal_of_world(source, k, I.Initialize{m, c, s, pi}, m, t, f, fact)
    case I.Serve{+m, c, +s, +r}: fact_literal_of_world(source, k, I.Serve{m, c, s, r}, m, t, f, fact)

def fact_canonical_of_world(~source: Source, -k: String, -x: I.Scenario, -m: Nat,
  -t: Nat, -f: I.Fact, input: L.E<{k == artifact(source) : String},
    L.E<{x == scenario(source, m) : I.Scenario}, of_route(source, x, t, f)>>) ->
  L.E<{k == artifact(source) : String},
    L.E<{x == scenario(source, m) : I.Scenario}, of_route(source, scenario(source, m), t, f)>>:
  match input:
    case L.Both{name, L.Both{equal, obs}}:
      L.Both{name, origin_canonical(source, x, scenario(source, m), t, f, equal, obs)}

def introduce_fact_literal(~source: Source, -k: String, x: I.Scenario, -t: Nat, -f: I.Fact,
  input: L.E<{k == artifact(source) : String},
    L.E<{x == scenario(source, world(x)) : I.Scenario}, of_route(source, x, t, f)>>) ->
  I.Happens(environment(source), k, x, t, f):
  match x:
    case I.Initialize{+m, c, +s, +pi}: fact_canonical_of_world(source, k, I.Initialize{m, c, s, pi}, m, t, f, input)
    case I.Serve{+m, c, +s, +r}: fact_canonical_of_world(source, k, I.Serve{m, c, s, r}, m, t, f, input)

# Executor result: equations of actual functions and the generated sequence.
# Receives no law/state preservation as a premise here.
def PrefixReal(~source: Source,
  -c: S.Configuration, -s: D.State, -r: P.Request, -ctx: D.Context,
  +origin: JudgmentSyntactic, -frames: List<&2, Q.FrameExec>) -> Type:
  &n: Nat -> {frames == Exec.generate(n,
    N.start(program(source, origin), ctx, I.arguments(r), s), S.schema(c)) : List<&2, Q.FrameExec>}

def FinalReal(~source: Source,
  -c: S.Configuration, -s: D.State, -r: P.Request, -ctx: D.Context,
  +origin: JudgmentSyntactic, -frames: List<&2, Q.FrameExec>, -prepared: N.Prepared) -> Type:
  &n: Nat -> &w: D.State -> &ts: List<&2, S.OperationEvent> -> &proposal: S.Response ->
    L.E<{frames == Exec.generate(n, N.start(program(source, origin), ctx, I.arguments(r), s),
      S.schema(c)) : List<&2, Q.FrameExec>},
      L.E<{N.traverse(n, N.start(program(source, origin), ctx, I.arguments(r), s), S.schema(c)) ==
        S.Final{w, ts, proposal} : S.Trace},
        {N.prepare(N.Stopped{w, ts, proposal}, c) == Some{prepared} : Maybe<&2, N.Prepared>}>>

def PointReal(~source: Source, -c: S.Configuration,
  -s: D.State, -r: P.Request, -ctx: D.Context, +origin: JudgmentSyntactic,
  point: R.PointExec) -> Type:
  match point:
    case R.BeforeOfStart{}: Unit
    case R.During{frames}: PrefixReal(source, c, s, r, ctx, origin, frames)
    case R.Prepared{frames, prepared}: FinalReal(source, c, s, r, ctx, origin, frames, prepared)

def OutputReal(~source: Source, -c: S.Configuration,
  -s: D.State, -r: P.Request, -ctx: D.Context, +origin: JudgmentSyntactic,
  output: R.OutputExecution) -> Type:
  match output:
    case R.Finalized{frames, prepared}: FinalReal(source, c, s, r, ctx, origin, frames, prepared)
    case R.ErrorExecution{point, stage, id, fatal}: PointReal(source, c, s, r, ctx, origin, point)
    case R.PendingExecution{point}: PointReal(source, c, s, r, ctx, origin, point)

# Tool approval supplies exact elaboration/derivation judgments and
# denotations of the two closed declarations actually checked.
# Grants no database law or post-publication state validity.
def JudgmentAccepted(~source: Source, -c: S.Configuration, -r: P.Request,
  -ctx: D.Context, +origin: JudgmentSyntactic) -> Type:
  L.E<elaboration(source, c, I.code(r), program(source, origin)),
    L.E<derivation(source, c, I.proof(r),
      Req.Certifies(c, I.code(r), program(source, origin), ctx, I.arguments(r))),
      L.E<Req.Certifies(c, I.code(r), program(source, origin), ctx, I.arguments(r)),
        L.E<derivation(source, c, I.proof(r), I.ProgramTerminates(c, program(source, origin))),
          I.ProgramTerminates(c, program(source, origin))>>>>

def JudgmentRefused(~source: Source, -c: S.Configuration, -r: P.Request,
  -ctx: D.Context) -> Type:
  @p: S.Program ->
    L.E<L.E<elaboration(source, c, I.code(r), p), I.ProgramTerminates(c, p)>,
      derivation(source, c, I.proof(r), Req.Certifies(c, I.code(r), p, ctx, I.arguments(r)))> -> Empty

def JudgmentClientReal(~source: Source, -c: S.Configuration, -r: P.Request,
  -ctx: D.Context, +origin: JudgmentSyntactic, judgment: R.Judgment) -> Type:
  match judgment:
    case R.Accepted{}: JudgmentAccepted(source, c, r, ctx, origin)
    case R.Refused{}: JudgmentRefused(source, c, r, ctx)
    case R.ErrorJudgment{id, fatal}: Unit
    case R.PendingJudgment{}: Unit

# Closed declaration denotations are needed only after
# the checker decision making them observable. They include no chronology.
def JudgmentOfPhase(~source: Source, -c: S.Configuration, +origin: JudgmentSyntactic,
  phase: R.PhaseBefore) -> Type:
  match phase:
    case R.AfterVerify{r, ctx}: JudgmentAccepted(source, c, r, ctx, origin)
    case R.Executing{r, ctx, qs}: JudgmentAccepted(source, c, r, ctx, origin)
    case R.AfterPrepare{r, ctx, qs, p}: JudgmentAccepted(source, c, r, ctx, origin)
    case _: Unit

def JudgmentOfBranch(~source: Source, -c: S.Configuration, +origin: JudgmentSyntactic,
  branch: R.Branch) -> Type:
  match branch:
    case R.GateRefusal{r, ctx, delivery}: JudgmentRefused(source, c, r, ctx)
    case R.Executed{r, ctx, qs, p, delivery}: JudgmentAccepted(source, c, r, ctx, origin)
    case R.FatalAfterPublication{r, ctx, qs, p, stage, id}: JudgmentAccepted(source, c, r, ctx, origin)
    case R.FailureBefore{phase, stage, id, fatal, delivery}: JudgmentOfPhase(source, c, origin, phase)
    case R.Pending{phase}: JudgmentOfPhase(source, c, origin, phase)
    case _: Unit

# Visible configuration is always the call's, independently of the route.
def configuration_of_origin(~source: Source,
  -c: S.Configuration, ini: Maybe<&2, D.State>, qs: List<&2, Q.Frame>,
  origin: Maybe<&2, JudgmentSyntactic>, t: Nat, -observed: S.Configuration,
  fact: of_origin(source, c, ini, qs, origin, t, I.ConfigurationInUse{observed})) ->
  {observed == c : S.Configuration}:
  match origin:
    case None{}: L.and_right({Q.position_observable(qs, t) == True{} : Bool}, {observed == c : S.Configuration}, fact)
    case Some{origin}: L.and_right({Q.position_observable(qs, t) == True{} : Bool}, {observed == c : S.Configuration}, fact)

def configuration_of_observation(~source: Source,
  -c: S.Configuration, data: ObservationData, t: Nat, -observed: S.Configuration,
  fact: of_observation(source, c, data, t, I.ConfigurationInUse{observed})) ->
  {observed == c : S.Configuration}:
  match data:
    case ObservationData{ini, qs, origin}:
      configuration_of_origin(source, c, ini, qs, origin, t, observed, fact)

def configuration_of_route(~source: Source, x: I.Scenario, t: Nat, -observed: S.Configuration,
  fact: of_route(source, x, t, I.ConfigurationInUse{observed})) ->
  {observed == I.configuration(x) : S.Configuration}:
  match x:
    case I.Initialize{+m, c, +s, pi}:
      configuration_of_observation(source, c, construct_initial(identity(source), c, s, initial(source, m)), t, observed, fact)
    case I.Serve{+m, c, +s, r}:
      configuration_of_observation(source, c, construct_call(c, s, r, call(source, m)), t, observed, fact)

law configuration_of_source:
  for ~source: Source
  for -k: String
  for x: I.Scenario
  for t: Nat
  for -observed: S.Configuration
  for fact: I.Happens(environment(source), k, x, t, I.ConfigurationInUse{observed})
  {observed == I.configuration(x) : S.Configuration}
def configuration_of_source(source, k, x, t, observed, fact):
  match x:
    case I.Initialize{+m, c, +s, +pi}:
      match fact:
        case L.Both{name, L.Both{canonical, obs}}:
          Equal.trans(S.Configuration, observed, I.configuration(scenario(source, m)), c,
            configuration_of_route(source, scenario(source, m), t, observed, obs),
            Equal.sym(S.Configuration, c, I.configuration(scenario(source, m)),
              Equal.cong(I.Scenario, S.Configuration, I.configuration, I.Initialize{m, c, s, pi}, scenario(source, m), canonical)))
    case I.Serve{+m, c, +s, +r}:
      match fact:
        case L.Both{name, L.Both{canonical, obs}}:
          Equal.trans(S.Configuration, observed, I.configuration(scenario(source, m)), c,
            configuration_of_route(source, scenario(source, m), t, observed, obs),
            Equal.sym(S.Configuration, c, I.configuration(scenario(source, m)),
              Equal.cong(I.Scenario, S.Configuration, I.configuration, I.Serve{m, c, s, r}, scenario(source, m), canonical)))

# Terms below denote the TWO closed declarations actually
# checked: Bindings.certificate and Bindings.terminates. Source fixes
# their bodies/targets; the tool contract links original derivation
# to those terms. There is no arbitrary Type eliminator, new axiom or
# Law4/Rule4/published-validity callback.
def certificate_of_judgment(~source: Source, -c: S.Configuration,
  -r: P.Request, -ctx: D.Context, +origin: JudgmentSyntactic,
  judgment: JudgmentAccepted(source, c, r, ctx, origin)) ->
  I.CertificateValid(environment(source), c, r, ctx, program(source, origin)):
  match judgment:
    case L.Both{elaborated, L.Both{derived, L.Both{certificate, L.Both{td, terminates}}}}:
      L.Both{L.Both{elaborated, terminates}, L.Both{derived, certificate}}

# Initialization: only the closed seed-validity declaration, never
# validity of a state published after executing a transaction.
def JudgmentInitialReal(~source: Source, -c: S.Configuration, -s: D.State,
  -pi: String, judgment: R.Judgment) -> Type:
  match judgment:
    case R.Accepted{}: L.E<derivation(source, c, pi, Req.Valid(c, s)), Req.Valid(c, s)>
    case _: Unit

def initial_become_accepted(~source: Source, -c: S.Configuration, -s: D.State,
  -pi: String, +judgment: R.Judgment, equal: {judgment == R.Accepted{} : R.Judgment},
  origin: JudgmentInitialReal(source, c, s, pi, judgment)) ->
  L.E<derivation(source, c, pi, Req.Valid(c, s)), Req.Valid(c, s)>:
  %equal : JudgmentInitialReal(source, c, s, pi, _)
  origin

# The message may fail. If it returns InputReady, the private snapshot matches
# what the controller published; identity is computed, not assumed.
def ready_snapshot(-s: D.State, -decoded: D.State, -r: P.Request,
  -br: List<&2, U32>, -cap: Maybe<&2, B.Number64>,
  faithful: Messages.LimitMessageFaithful(E.InputReady{decoded, r}, s, br, cap)) ->
  {decoded == s : D.State}:
  match faithful:
    case (ceiling, L.Both{measure, L.Both{same, request}}): same

law message_ready_preserves_snapshot:
  for +cap: Maybe<&2, B.Number64>
  for +br: List<&2, U32>
  for +s: D.State
  for -decoded: D.State
  for -r: P.Request
  for ready: {E.read_message(cap, br, s) == E.InputReady{decoded, r} : E.PreAuthentication}
  {decoded == s : D.State}
def message_ready_preserves_snapshot(cap, br, s, decoded, r, ready):
  ready_snapshot(s, decoded, r, br, cap,
    (%ready : Messages.LimitMessageFaithful(_, s, br, cap)
      Messages.read_message_faithful(cap, br, s)))

law authenticate_packet_uses_snapshot_canonical:
  for +cap: Maybe<&2, B.Number64>
  for +br: List<&2, U32>
  for +s: D.State
  for +decoded: D.State
  for +r: P.Request
  for -pre: E.PreAuthentication
  for canonical: {pre == E.read_message(cap, br, s) : E.PreAuthentication}
  for ready: {pre == E.InputReady{decoded, r} : E.PreAuthentication}
  {D.authenticate(decoded, I.credential(r)) == D.authenticate(s, I.credential(r)) : Maybe<&2, D.Context>}
def authenticate_packet_uses_snapshot_canonical(cap, br, s, decoded, r, pre, canonical, ready):
  Equal.cong(D.State, Maybe<&2, D.Context>, state => D.authenticate(state, I.credential(r)), decoded, s,
    message_ready_preserves_snapshot(cap, br, s, decoded, r,
      Equal.trans(E.PreAuthentication, E.read_message(cap, br, s), pre, E.InputReady{decoded, r},
        Equal.sym(E.PreAuthentication, pre, E.read_message(cap, br, s), canonical), ready)))

# Literal observation is linked to the sole canonical route by the same J.
def introduce_initial_of_route(~source: Source, ~c: S.Configuration, +world: Nat,
  +s: D.State, +pi: String, +cf: JudgmentSyntactic, +sf: JudgmentSyntactic,
  +pf: JudgmentSyntactic, +j: R.Judgment, +result: R.ResultInitial, +micro: R.Micro, +t: Nat, -f: I.Fact,
  canonical: {I.Initialize{world, c, s, pi} == scenario(source, world) : I.Scenario},
  origin: {initial(source, world) == InitialData{cf, sf, pf, j, result, micro} : InitialData},
  obs: Q.observes_service(c, without_program(), None{}, R.generate_result_initial(c, identity(source), s, j, result, micro), t, f)) ->
  I.Happens(environment(source), artifact(source), I.Initialize{world, c, s, pi}, t, f):
  L.Both{{==},
    (%canonical : L.E<{I.Initialize{world, c, s, pi} == _ : I.Scenario}, of_route(source, _, t, f)>
      L.Both{{==},
        (%Equal.sym(InitialData, initial(source, world), InitialData{cf, sf, pf, j, result, micro}, origin) :
          of_observation(source, c, construct_initial(identity(source), c, s, _), t, f) obs)})}

def start_of_query(~source: Source, ~c: S.Configuration, +world: Nat,
  +s: D.State, +pi: String, +cf: JudgmentSyntactic, +sf: JudgmentSyntactic,
  +pf: JudgmentSyntactic, +micro: R.Micro,
  canonical: {I.Initialize{world, c, s, pi} == scenario(source, world) : I.Scenario},
  origin: {initial(source, world) == InitialData{cf, sf, pf, R.Accepted{}, R.InitializationFinished{}, micro} : InitialData},
  query_result: &t: Nat -> {Q.query(R.generate_initial(c, identity(source), s, R.Accepted{}, micro), t) == Some{Q.Initialized{s}} : Maybe<&2, Q.Frame>}) ->
  I.InSomeMoment(environment(source), artifact(source), I.Initialize{world, c, s, pi}, I.InstanceStarted{s}):
  match query_result:
    case (+t, obtained):
      (t, introduce_initial_of_route(source, c, world, s, pi, cf, sf, pf, R.Accepted{}, R.InitializationFinished{}, micro, t, I.InstanceStarted{s}, canonical, origin,
        Q.query_establishes_observation(c, without_program(), R.generate_initial(c, identity(source), s, R.Accepted{}, micro),
          t, Q.Initialized{s}, I.InstanceStarted{s}, obtained, {==})))

law initialization_approved_reaches_start:
  for ~source: Source
  for ~c: S.Configuration
  for +world: Nat
  for +s: D.State
  for +pi: String
  for +cf: JudgmentSyntactic
  for +sf: JudgmentSyntactic
  for +pf: JudgmentSyntactic
  for +micro: R.Micro
  for canonical: {I.Initialize{world, c, s, pi} == scenario(source, world) : I.Scenario}
  for origin: {initial(source, world) == InitialData{cf, sf, pf, R.Accepted{}, R.InitializationFinished{}, micro} : InitialData}
  for configured: {Config.is_valid(c, identity(source)) == True{} : Bool}
  for valid: Req.Valid(c, s)
  I.InSomeMoment(environment(source), artifact(source), I.Initialize{world, c, s, pi}, I.InstanceStarted{s})
def initialization_approved_reaches_start(source, c, world, s, pi, cf, sf, pf, micro, canonical, origin, configured, valid):
  start_of_query(source, c, world, s, pi, cf, sf, pf, micro, canonical, origin,
    Phases.seed_valid_has_instance_after_approval(c, identity(source), s, micro, configured, valid))

# Request origin is the second ACTUAL block assembled in the private pipe.
# Does not assumes decoder or authentication returned the correct request.
def link_body_received(-bs: List<&2, U32>, +be: List<&2, U32>, +br: List<&2, U32>,
  -r: P.Request, -world: Nat, -c: S.Configuration, -s: D.State, -input: X.Reception,
  separate: {T.separate(bs) == Some{T.Parts{be, br}} : Maybe<&2, T.Parts>},
  received: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition},
  origin: Messages.BodyForInterface(bs, r, world, c, s, input)) ->
  I.RequestReceived(I.Serve{world, c, s, input}, r):
  match origin:
    case (+be2, +br2, L.Both{separate2, L.Both{canonical, link}}):
      link(Equal.trans(X.Disposition, X.decide_reception(c, input), X.ProcessBody{br}, X.ProcessBody{br2}, received,
        Equal.cong(List<&2, U32>, X.Disposition, body => X.ProcessBody{body}, br, br2,
          Equal.cong(T.Parts, List<&2, U32>, Transport.second, T.Parts{be, br}, T.Parts{be2, br2},
            F.some_injective(T.Parts, T.Parts{be, br}, T.Parts{be2, br2},
              Equal.trans(Maybe<&2, T.Parts>, Some{T.Parts{be, br}}, T.separate(bs), Some{T.Parts{be2, br2}},
                Equal.sym(Maybe<&2, T.Parts>, T.separate(bs), Some{T.Parts{be, br}}, separate), separate2))))))

law request_ready_came_of_body:
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +bs: List<&2, U32>
  for +e: D.Schema
  for +l: S.Limits
  for +s: D.State
  for +r: P.Request
  for -world: Nat
  for -c: S.Configuration
  for +input: X.Reception
  for assembly: {T.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for octets_and: {B.octets_all_valid(be) == True{} : Bool}
  for octets_r: {B.octets_all_valid(br) == True{} : Bool}
  for received: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition}
  for ready: {E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication}
  I.RequestReceived(I.Serve{world, c, s, input}, r)
def request_ready_came_of_body(be, br, bs, e, l, s, r, world, c, input, assembly, octets_and, octets_r, received, ready):
  link_body_received(bs, be, br, r, world, c, s, input,
    Transport.separate_inverts_all_assembly_is_valid(be, br, bs, assembly, octets_and, octets_r), received,
    Messages.ready_provides_body_and_linkage_to_interface_original(bs, e, l, s, r, world, c, input, ready))
