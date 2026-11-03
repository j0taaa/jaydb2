# Initialization/configuration: content follows from the checked initial term;
# order/exclusion follows from the actual renderer. Receives no Rule1.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/LAWS.bend as K
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ./SourceService.bend as Source
import ./RoutesService.bend as R
import ./ProtocolService.bend as Q
import ./PhasesService.bend as Phases
import ./Configuration.bend as Configuration
import ../src/ConfigurationCheck.bend as Config
import ./Call.bend as Call
import ../contract/Resources.bend as X
import ./RefinementService.bend as Ref
import ./ScenariosService.bend as C
import ./HistoryService.bend as H
import ./ModelService.bend as Model

# The accepted branch never emits initial rejection, including in microframes.
def encoding_without_refusal(q: Maybe<&2, List<&2, U32>>, -s: D.State) ->
  {Phases.absent(Phases.RefusalInitial{}, R.render_initial(q, s)) == True{} : Bool}:
  match q:
    case None{}: {==}
    case Some{bs}: {==}

def start_accepted_without_refusal(+m: R.Micro, +s: D.State) ->
  {Phases.absent(Phases.RefusalInitial{}, R.render(m, s, R.InitialOk{})) == True{} : Bool}:
  Phases.concatenate_absence(Phases.RefusalInitial{}, R.micro_output(m), R.render_initial(P.encode(D.state_value(s)), s),
    Phases.micro_output_without_macros(Phases.RefusalInitial{}, m), encoding_without_refusal(P.encode(D.state_value(s)), s))

def refusal_excludes_start(+m: R.Micro, +s: D.State, +j: R.Judgment, +result: R.ResultInitial, +is_valid: Bool,
  +t: Nat, +status: S.Status, refusal: {Q.query(R.render(m, s, R.decide_judgment_initial(j, result, is_valid)), t) == Some{Q.InitialRefused{status}} : Maybe<&2, Q.Frame>},
  u: Nat, +w: D.State, started: {Q.query(R.render(m, s, R.decide_judgment_initial(j, result, is_valid)), u) == Some{Q.Initialized{w}} : Maybe<&2, Q.Frame>}) -> Empty:
  match j:
    case R.Accepted{}:
      match result:
        case R.InitializationFinished{}:
          match is_valid:
            case False{}:
              Phases.absent_excludes_query(Phases.Initialization{}, [Q.Configured{}, Q.InitialRefused{S.DataError{}}], u, Q.Initialized{w}, {==}, {==}, started)
            case True{}:
              Phases.absent_excludes_query(Phases.RefusalInitial{}, R.render(m, s, R.InitialOk{}), t, Q.InitialRefused{status}, start_accepted_without_refusal(m, s), {==}, refusal)
        case R.FailedInitial{accepts, stage, id, fatal}:
          Phases.absent_excludes_query(Phases.Initialization{}, R.render(m, s, R.InitialFailure{accepts && is_valid, stage, id, fatal}), u, Q.Initialized{w}, Phases.failure_initial_without_instance(m, s, accepts && is_valid, stage, id, fatal), {==}, started)
        case R.PendingInitial{accepts}:
          Phases.absent_excludes_query(Phases.Initialization{}, R.render(m, s, R.InitialPending{accepts && is_valid}), u, Q.Initialized{w}, Phases.pending_initial_without_instance(m, s, accepts && is_valid), {==}, started)
    case R.Refused{}:
      Phases.absent_excludes_query(Phases.Initialization{}, [Q.Configured{}, Q.InitialRefused{S.Certificate{}}], u, Q.Initialized{w}, {==}, {==}, started)
    case R.ErrorJudgment{id, fatal}:
      Phases.absent_excludes_query(Phases.Initialization{}, R.render(m, s, R.InitialFailure{False{}, X.Verify{}, id, fatal}), u, Q.Initialized{w}, Phases.failure_initial_without_instance(m, s, False{}, X.Verify{}, id, fatal), {==}, started)
    case R.PendingJudgment{}:
      Phases.absent_excludes_query(Phases.Initialization{}, R.render(m, s, R.InitialPending{False{}}), u, Q.Initialized{w}, Phases.pending_initial_without_instance(m, s, False{}), {==}, started)

def content_after_classify(~source: Source.Source, ~c: S.Configuration,
  -world: Nat, +s: D.State, +pi: String, +j: R.Judgment,
  category: L.E<{Config.is_valid(c, Source.identity(source)) == True{} : Bool}, {j == R.Accepted{} : R.Judgment}>,
  origin: Source.JudgmentInitialReal(source, c, s, pi, j)) ->
  K.ProofInitialCorrect(I.Initialize{world, c, s, pi}, Source.environment(source)):
  match category:
    case L.Both{configured, accepted}:
      L.Both{Configuration.accepts_satisfies_configuration_is_valid_original(Source.environment(source), c, configured),
        Source.initial_become_accepted(source, c, s, pi, j, accepted, origin)}

law proof_initial_accepts_and_correct:
  for ~source: Source.Source
  for ~c: S.Configuration
  for -world: Nat
  for +s: D.State
  for +pi: String
  for +j: R.Judgment
  for +result: R.ResultInitial
  for +m: R.Micro
  for +t: Nat
  for origin: Source.JudgmentInitialReal(source, c, s, pi, j)
  for query_result: {Q.query(R.generate_result_initial(c, Source.identity(source), s, j, result, m), t) == Some{Q.InitialAccepts{}} : Maybe<&2, Q.Frame>}
  K.ProofInitialCorrect(I.Initialize{world, c, s, pi}, Source.environment(source))
def proof_initial_accepts_and_correct(source, c, world, s, pi, j, result, m, t, origin, query_result):
  content_after_classify(source, c, world, s, pi, j,
    Phases.start_result_requires_configuration_and_judgment_accepted(m, s, Config.is_valid(c, Source.identity(source)), j, result, t, Q.InitialAccepts{}, {==}, query_result), origin)

def start_combined_content(~source: Source.Source, ~c: S.Configuration,
  -world: Nat, -s: D.State, -pi: String, -t: Nat, -w: D.State,
  content: K.ProofInitialCorrect(I.Initialize{world, c, s, pi}, Source.environment(source)),
  same: {w == s : D.State},
  proof_before: I.Before(Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.ProofInitialAccepts{})) ->
  K.StartCorrect(I.Initialize{world, c, s, pi}, Source.environment(source), Source.artifact(source), t, w):
  match content:
    case L.Both{configured, L.Both{derived, valid}}:
      L.Both{configured, L.Both{derived, L.Both{valid, L.Both{same, proof_before}}}}

def proof_previous_in_model(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +pi: String, +cf: Source.JudgmentSyntactic,
  +sf: Source.JudgmentSyntactic, +pf: Source.JudgmentSyntactic, +m: R.Micro, -t: Nat,
  canonical: {I.Initialize{world, c, s, pi} == Source.scenario(source, world) : I.Scenario},
  origin: {Source.initial(source, world) == Source.InitialData{cf, sf, pf, R.Accepted{}, R.InitializationFinished{}, m} : Source.InitialData},
  configured: {Config.is_valid(c, Source.identity(source)) == True{} : Bool},
  before: &u: Nat -> L.E<{Nat.is_lt(u, t) == True{} : Bool},
    {Q.query(R.render(m, s, R.InitialOk{}), u) == Some{Q.InitialAccepts{}} : Maybe<&2, Q.Frame>}>) ->
  I.Before(Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.ProofInitialAccepts{}):
  match before:
    case (+u, L.Both{order, query_result}):
      (u, L.Both{order, Source.introduce_initial_of_route(source, c, world, s, pi, cf, sf, pf, R.Accepted{}, R.InitializationFinished{}, m, u, I.ProofInitialAccepts{}, canonical, origin,
        (%Equal.sym(Bool, Config.is_valid(c, Source.identity(source)), True{}, configured) :
          Q.observes_service(c, Source.without_program(), None{}, R.render(m, s, R.decide_initial_cases(_, R.Accepted{})), u, I.ProofInitialAccepts{})
          Q.query_establishes_observation(c, Source.without_program(), R.render(m, s, R.InitialOk{}), u,
            Q.InitialAccepts{}, I.ProofInitialAccepts{}, query_result, {==})))})

def start_of_queries(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +pi: String, +cf: Source.JudgmentSyntactic,
  +sf: Source.JudgmentSyntactic, +pf: Source.JudgmentSyntactic, +m: R.Micro, +t: Nat, +w: D.State,
  canonical: {I.Initialize{world, c, s, pi} == Source.scenario(source, world) : I.Scenario},
  origin: {Source.initial(source, world) == Source.InitialData{cf, sf, pf, R.Accepted{}, R.InitializationFinished{}, m} : Source.InitialData},
  values: Source.JudgmentInitialReal(source, c, s, pi, R.Accepted{}),
  flags: L.E<{Config.is_valid(c, Source.identity(source)) == True{} : Bool}, {Config.is_valid(c, Source.identity(source)) == True{} : Bool}>,
  queries: L.E<{Q.query(R.render(m, s, R.InitialOk{}), t) == Some{Q.Initialized{w}} : Maybe<&2, Q.Frame>},
    {Q.query(R.render(m, s, R.InitialOk{}), t) == Some{Q.Initialized{w}} : Maybe<&2, Q.Frame>}>) ->
  K.StartCorrect(I.Initialize{world, c, s, pi}, Source.environment(source), Source.artifact(source), t, w):
  match flags queries:
    case L.Both{cfg1, cfg2} L.Both{one, two}:
      start_combined_content(source, c, world, s, pi, t, w,
        L.Both{Configuration.accepts_satisfies_configuration_is_valid_original(Source.environment(source), c, cfg1), values},
        Phases.initialization_only_starts_seed(m, s, t, w, one),
        proof_previous_in_model(source, c, world, s, pi, cf, sf, pf, m, t, canonical, origin, cfg2,
          Phases.instance_only_starts_after_proof_initial(m, s, t, w, two)))

law instance_accepts_and_correct:
  for ~source: Source.Source
  for ~c: S.Configuration
  for +world: Nat
  for +s: D.State
  for +pi: String
  for +cf: Source.JudgmentSyntactic
  for +sf: Source.JudgmentSyntactic
  for +pf: Source.JudgmentSyntactic
  for +m: R.Micro
  for +t: Nat
  for +w: D.State
  for canonical: {I.Initialize{world, c, s, pi} == Source.scenario(source, world) : I.Scenario}
  for origin: {Source.initial(source, world) == Source.InitialData{cf, sf, pf, R.Accepted{}, R.InitializationFinished{}, m} : Source.InitialData}
  for configured: {Config.is_valid(c, Source.identity(source)) == True{} : Bool}
  for values: Source.JudgmentInitialReal(source, c, s, pi, R.Accepted{})
  for query_result: {Q.query(R.render(m, s, R.InitialOk{}), t) == Some{Q.Initialized{w}} : Maybe<&2, Q.Frame>}
  K.StartCorrect(I.Initialize{world, c, s, pi}, Source.environment(source), Source.artifact(source), t, w)
def instance_accepts_and_correct(source, c, world, s, pi, cf, sf, pf, m, t, w, canonical, origin, configured, values, query_result):
  start_of_queries(source, c, world, s, pi, cf, sf, pf, m, t, w, canonical, origin, values,
    Call.duplicate_equality(Bool, Config.is_valid(c, Source.identity(source)), True{}, configured),
    Call.duplicate_equality(Maybe<&2, Q.Frame>, Q.query(R.render(m, s, R.InitialOk{}), t), Some{Q.Initialized{w}}, query_result))

law refusal_initial_excludes_instance:
  for ~source: Source.Source
  for ~c: S.Configuration
  for +world: Nat
  for +s: D.State
  for +pi: String
  for +m: R.Micro
  for +is_valid: Bool
  for +j: R.Judgment
  for +result: R.ResultInitial
  for +t: Nat
  for +status: S.Status
  for refusal: {Q.query(R.render(m, s, R.decide_judgment_initial(j, result, is_valid)), t) == Some{Q.InitialRefused{status}} : Maybe<&2, Q.Frame>}
  for extract_start: @u: Nat -> @w: D.State -> I.Happens(Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, u, I.InstanceStarted{w}) ->
    {Q.query(R.render(m, s, R.decide_judgment_initial(j, result, is_valid)), u) == Some{Q.Initialized{w}} : Maybe<&2, Q.Frame>}
  K.Rule1(I.InitializationRefused{status}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t)
def refusal_initial_excludes_instance(source, c, world, s, pi, m, is_valid, j, result, t, status, refusal, extract_start):
  +u => +w => started => refusal_excludes_start(m, s, j, result, is_valid, t, status, refusal, u, w, extract_start(u, w, started))

# Actual facts of the same initialization preserve the same generated list.
def extract_start_literal(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +pi: String, +cf: Source.JudgmentSyntactic,
  +sf: Source.JudgmentSyntactic, +pf: Source.JudgmentSyntactic, +j: R.Judgment, +result: R.ResultInitial,
  +m: R.Micro, +u: Nat, +w: D.State,
  origin: {Source.initial(source, world) == Source.InitialData{cf, sf, pf, j, result, m} : Source.InitialData},
  literal: L.E<{Source.artifact(source) == Source.artifact(source) : String},
    L.E<{I.Initialize{world, c, s, pi} == Source.scenario(source, world) : I.Scenario},
      Source.of_route(source, I.Initialize{world, c, s, pi}, u, I.InstanceStarted{w})>>) ->
  {Q.query(R.generate_result_initial(c, Source.identity(source), s, j, result, m), u) == Some{Q.Initialized{w}} : Maybe<&2, Q.Frame>}:
  match literal:
    case L.Both{name, L.Both{canonical, obs}}:
      Q.observation_frame(c, Source.without_program(), R.generate_result_initial(c, Source.identity(source), s, j, result, m), u, I.InstanceStarted{w},
        (%origin : Source.of_observation(source, c, Source.construct_initial(Source.identity(source), c, s, _), u, I.InstanceStarted{w}) obs))

def extract_start(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +pi: String, +cf: Source.JudgmentSyntactic,
  +sf: Source.JudgmentSyntactic, +pf: Source.JudgmentSyntactic, +j: R.Judgment, +result: R.ResultInitial,
  +m: R.Micro, +u: Nat, +w: D.State,
  origin: {Source.initial(source, world) == Source.InitialData{cf, sf, pf, j, result, m} : Source.InitialData},
  fact: I.Happens(Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, u, I.InstanceStarted{w})) ->
  {Q.query(R.generate_result_initial(c, Source.identity(source), s, j, result, m), u) == Some{Q.Initialized{w}} : Maybe<&2, Q.Frame>}:
  extract_start_literal(source, c, world, s, pi, cf, sf, pf, j, result, m, u, w, origin,
    Source.eliminate_fact_literal(source, Source.artifact(source), I.Initialize{world, c, s, pi}, u, I.InstanceStarted{w}, fact))

def instance_of_branch(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +pi: String, +cf: Source.JudgmentSyntactic,
  +sf: Source.JudgmentSyntactic, +pf: Source.JudgmentSyntactic, +j: R.Judgment, +result: R.ResultInitial, +is_valid: Bool,
  +m: R.Micro, +t: Nat, +w: D.State,
  exact: {Config.is_valid(c, Source.identity(source)) == is_valid : Bool},
  canonical: {I.Initialize{world, c, s, pi} == Source.scenario(source, world) : I.Scenario},
  origin: {Source.initial(source, world) == Source.InitialData{cf, sf, pf, j, result, m} : Source.InitialData},
  values: Source.JudgmentInitialReal(source, c, s, pi, j),
  query_result: {Q.query(R.render(m, s, R.decide_judgment_initial(j, result, is_valid)), t) == Some{Q.Initialized{w}} : Maybe<&2, Q.Frame>}) ->
  K.StartCorrect(I.Initialize{world, c, s, pi}, Source.environment(source), Source.artifact(source), t, w):
  match j:
    case R.Accepted{}:
      match result:
        case R.InitializationFinished{}:
          match is_valid:
            case False{}:
              L.ex_false(K.StartCorrect(I.Initialize{world, c, s, pi}, Source.environment(source), Source.artifact(source), t, w),
            Phases.absent_excludes_query(Phases.Initialization{}, [Q.Configured{}, Q.InitialRefused{S.DataError{}}], t, Q.Initialized{w}, {==}, {==}, query_result))
            case True{}:
              instance_accepts_and_correct(source, c, world, s, pi, cf, sf, pf, m, t, w, canonical, origin, exact, values, query_result)
        case R.FailedInitial{accepts, stage, id, fatal}:
          L.ex_false(K.StartCorrect(I.Initialize{world, c, s, pi}, Source.environment(source), Source.artifact(source), t, w),
            Phases.absent_excludes_query(Phases.Initialization{}, R.render(m, s, R.InitialFailure{accepts && is_valid, stage, id, fatal}), t, Q.Initialized{w}, Phases.failure_initial_without_instance(m, s, accepts && is_valid, stage, id, fatal), {==}, query_result))
        case R.PendingInitial{accepts}:
          L.ex_false(K.StartCorrect(I.Initialize{world, c, s, pi}, Source.environment(source), Source.artifact(source), t, w),
            Phases.absent_excludes_query(Phases.Initialization{}, R.render(m, s, R.InitialPending{accepts && is_valid}), t, Q.Initialized{w}, Phases.pending_initial_without_instance(m, s, accepts && is_valid), {==}, query_result))
    case R.Refused{}:
      L.ex_false(K.StartCorrect(I.Initialize{world, c, s, pi}, Source.environment(source), Source.artifact(source), t, w),
            Phases.absent_excludes_query(Phases.Initialization{}, [Q.Configured{}, Q.InitialRefused{S.Certificate{}}], t, Q.Initialized{w}, {==}, {==}, query_result))
    case R.ErrorJudgment{id, fatal}:
      L.ex_false(K.StartCorrect(I.Initialize{world, c, s, pi}, Source.environment(source), Source.artifact(source), t, w),
            Phases.absent_excludes_query(Phases.Initialization{}, R.render(m, s, R.InitialFailure{False{}, X.Verify{}, id, fatal}), t, Q.Initialized{w}, Phases.failure_initial_without_instance(m, s, False{}, X.Verify{}, id, fatal), {==}, query_result))
    case R.PendingJudgment{}:
      L.ex_false(K.StartCorrect(I.Initialize{world, c, s, pi}, Source.environment(source), Source.artifact(source), t, w),
            Phases.absent_excludes_query(Phases.Initialization{}, R.render(m, s, R.InitialPending{False{}}), t, Q.Initialized{w}, Phases.pending_initial_without_instance(m, s, False{}), {==}, query_result))

def instance_combined_metadata(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +pi: String, +cf: Source.JudgmentSyntactic,
  +sf: Source.JudgmentSyntactic, +pf: Source.JudgmentSyntactic, +j: R.Judgment, +result: R.ResultInitial,
  +m: R.Micro, +t: Nat, +w: D.State,
  canonical: {I.Initialize{world, c, s, pi} == Source.scenario(source, world) : I.Scenario},
  origins: L.E<{Source.initial(source, world) == Source.InitialData{cf, sf, pf, j, result, m} : Source.InitialData},
    {Source.initial(source, world) == Source.InitialData{cf, sf, pf, j, result, m} : Source.InitialData}>,
  values: Source.JudgmentInitialReal(source, c, s, pi, j),
  fact: Source.of_route(source, I.Initialize{world, c, s, pi}, t, I.InstanceStarted{w})) ->
  K.StartCorrect(I.Initialize{world, c, s, pi}, Source.environment(source), Source.artifact(source), t, w):
  match origins:
    case L.Both{real, read}:
      instance_of_branch(source, c, world, s, pi, cf, sf, pf, j, result, Config.is_valid(c, Source.identity(source)), m, t, w, {==}, canonical, real, values,
        Q.observation_frame(c, Source.without_program(), R.generate_result_initial(c, Source.identity(source), s, j, result, m), t, I.InstanceStarted{w},
          (%read : Source.of_observation(source, c, Source.construct_initial(Source.identity(source), c, s, _), t, I.InstanceStarted{w}) fact)))

# Origin is only the judgment of pure initialization modules.
def JudgmentOfData(~source: Source.Source, -c: S.Configuration, -s: D.State,
  -pi: String, data: Source.InitialData) -> Type:
  match data:
    case Source.InitialData{cf, sf, pf, j, result, micro}: Source.JudgmentInitialReal(source, c, s, pi, j)

def refusal_combined_metadata(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +pi: String, +cf: Source.JudgmentSyntactic,
  +sf: Source.JudgmentSyntactic, +pf: Source.JudgmentSyntactic, +j: R.Judgment, +result: R.ResultInitial,
  +m: R.Micro, +t: Nat, +status: S.Status,
  origins: L.E<{Source.initial(source, world) == Source.InitialData{cf, sf, pf, j, result, m} : Source.InitialData},
    {Source.initial(source, world) == Source.InitialData{cf, sf, pf, j, result, m} : Source.InitialData}>,
  fact: Source.of_route(source, I.Initialize{world, c, s, pi}, t, I.InitializationRefused{status})) ->
  K.Rule1(I.InitializationRefused{status}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t):
  match origins:
    case L.Both{read, real}:
      refusal_initial_excludes_instance(source, c, world, s, pi, m, Config.is_valid(c, Source.identity(source)), j, result, t, status,
        Q.observation_frame(c, Source.without_program(), R.generate_result_initial(c, Source.identity(source), s, j, result, m), t, I.InitializationRefused{status},
          (%read : Source.of_observation(source, c, Source.construct_initial(Source.identity(source), c, s, _), t, I.InitializationRefused{status}) fact)),
        +u => +w => start => extract_start(source, c, world, s, pi, cf, sf, pf, j, result, m, u, w, real, start))

def rule1_initial_data(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +pi: String, data: Source.InitialData, +t: Nat, f: I.Fact,
  canonical: {I.Initialize{world, c, s, pi} == Source.scenario(source, world) : I.Scenario},
  origin: {Source.initial(source, world) == data : Source.InitialData},
  values: JudgmentOfData(source, c, s, pi, data),
  fact: Source.of_route(source, I.Initialize{world, c, s, pi}, t, f)) ->
  K.Rule1(f, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t):
  match data:
    case Source.InitialData{+cf, +sf, +pf, +j, +result, +m}:
      match f:
        case I.ConfigurationInUse{observed}:
          Source.configuration_of_route(source, I.Initialize{world, c, s, pi}, t, observed, fact)
        case I.InstanceStarted{+w}:
          instance_combined_metadata(source, c, world, s, pi, cf, sf, pf, j, result, m, t, w, canonical,
            Call.duplicate_equality(Source.InitialData, Source.initial(source, world), Source.InitialData{cf, sf, pf, j, result, m}, origin), values, fact)
        case I.ProofInitialAccepts{}:
          proof_initial_accepts_and_correct(source, c, world, s, pi, j, result, m, t, values,
            Q.observation_frame(c, Source.without_program(), R.generate_result_initial(c, Source.identity(source), s, j, result, m), t, I.ProofInitialAccepts{},
              (%origin : Source.of_observation(source, c, Source.construct_initial(Source.identity(source), c, s, _), t, I.ProofInitialAccepts{}) fact)))
        case I.InitializationRefused{+status}:
          refusal_combined_metadata(source, c, world, s, pi, cf, sf, pf, j, result, m, t, status,
            Call.duplicate_equality(Source.InitialData, Source.initial(source, world), Source.InitialData{cf, sf, pf, j, result, m}, origin), fact)
        case I.InspectionNotModeled{_a0}: Unit{}
        case I.EffectNotModeled{_a0}: Unit{}
        case I.Encoded{_a0, _a1}: Unit{}
        case I.Decoded{_a0, _a1}: Unit{}
        case I.Stored{_a0, _a1, _a2}: Unit{}
        case I.Operated{_a0, _a1, _a2, _a3}: Unit{}
        case I.CheckedLength{_a0, _a1}: Unit{}
        case I.AllocatedField{_a0, _a1}: Unit{}
        case I.ReadBody{_a0, _a1, _a2}: Unit{}
        case I.ReceivedRequest{_a0}: Unit{}
        case I.Authenticated{_a0, _a1}: Unit{}
        case I.CertificateAccepted{_a0, _a1, _a2}: Unit{}
        case I.CertificateRejected{_a0, _a1}: Unit{}
        case I.ProgramStarted{_a0, _a1, _a2}: Unit{}
        case I.Evaluated{_a0, _a1, _a2, _a3}: Unit{}
        case I.Prepared{_a0, _a1}: Unit{}
        case I.Published{_a0}: Unit{}
        case I.StateVisible{_a0}: Unit{}
        case I.FailedEnvironment{_a0, _a1, _a2}: Unit{}
        case I.Concluded{_a0, _a1, _a2}: Unit{}
        case I.DeliveredEverything{_a0}: Unit{}
        case I.DeliveryInterrupted{_a0}: Unit{}
        case I.ClosedChannel{}: Unit{}
        case I.NextCall{_a0, _a1}: Unit{}

def negate_instance_serve(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +reception: X.Reception, data: Source.CallData,
  +t: Nat, +w: D.State, origin: {Source.call(source, world) == data : Source.CallData},
  fact: Source.of_route(source, I.Serve{world, c, s, reception}, t, I.InstanceStarted{w})) -> Empty:
  match data:
    case Source.CallData{cf, +ps, cert, terminates, +bs, +tools, +micro}:
      Phases.absent_excludes_query(Phases.StartWithProof{}, R.generate(c, reception, bs, s, tools, micro), t, Q.Initialized{w},
        Phases.service_without_start_combined_proof(c, reception, bs, s, tools, micro), {==},
        Q.observation_frame(c, Source.program(source, ps), R.generate(c, reception, bs, s, tools, micro), t, I.InstanceStarted{w},
          (%origin : Source.of_observation(source, c, Source.construct_call(c, s, reception, _), t, I.InstanceStarted{w}) fact)))

def negate_proof_serve(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +reception: X.Reception, data: Source.CallData,
  +t: Nat, origin: {Source.call(source, world) == data : Source.CallData},
  fact: Source.of_route(source, I.Serve{world, c, s, reception}, t, I.ProofInitialAccepts{})) -> Empty:
  match data:
    case Source.CallData{cf, +ps, cert, terminates, +bs, +tools, +micro}:
      Phases.absent_excludes_query(Phases.StartWithProof{}, R.generate(c, reception, bs, s, tools, micro), t, Q.InitialAccepts{},
        Phases.service_without_start_combined_proof(c, reception, bs, s, tools, micro), {==},
        Q.observation_frame(c, Source.program(source, ps), R.generate(c, reception, bs, s, tools, micro), t, I.ProofInitialAccepts{},
          (%origin : Source.of_observation(source, c, Source.construct_call(c, s, reception, _), t, I.ProofInitialAccepts{}) fact)))

def rule1_serve_data(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +reception: X.Reception, +data: Source.CallData,
  +t: Nat, f: I.Fact, origin: {Source.call(source, world) == data : Source.CallData},
  fact: Source.of_route(source, I.Serve{world, c, s, reception}, t, f)) ->
  K.Rule1(f, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t):
  match f:
    case I.ConfigurationInUse{observed}:
      Source.configuration_of_route(source, I.Serve{world, c, s, reception}, t, observed, fact)
    case I.InstanceStarted{+w}: negate_instance_serve(source, c, world, s, reception, data, t, w, origin, fact)
    case I.ProofInitialAccepts{}: negate_proof_serve(source, c, world, s, reception, data, t, origin, fact)
    case I.InitializationRefused{status}:
      +u => +w => start => negate_instance_serve(source, c, world, s, reception, data, u, w, origin,
        Ref.remove_guards({Source.artifact(source) == Source.artifact(source) : String},
          {I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario},
          Source.of_route(source, I.Serve{world, c, s, reception}, u, I.InstanceStarted{w}), Source.eliminate_fact_literal(source, Source.artifact(source), I.Serve{world, c, s, reception}, u, I.InstanceStarted{w}, start)))
    case I.InspectionNotModeled{_a0}: Unit{}
    case I.EffectNotModeled{_a0}: Unit{}
    case I.Encoded{_a0, _a1}: Unit{}
    case I.Decoded{_a0, _a1}: Unit{}
    case I.Stored{_a0, _a1, _a2}: Unit{}
    case I.Operated{_a0, _a1, _a2, _a3}: Unit{}
    case I.CheckedLength{_a0, _a1}: Unit{}
    case I.AllocatedField{_a0, _a1}: Unit{}
    case I.ReadBody{_a0, _a1, _a2}: Unit{}
    case I.ReceivedRequest{_a0}: Unit{}
    case I.Authenticated{_a0, _a1}: Unit{}
    case I.CertificateAccepted{_a0, _a1, _a2}: Unit{}
    case I.CertificateRejected{_a0, _a1}: Unit{}
    case I.ProgramStarted{_a0, _a1, _a2}: Unit{}
    case I.Evaluated{_a0, _a1, _a2, _a3}: Unit{}
    case I.Prepared{_a0, _a1}: Unit{}
    case I.Published{_a0}: Unit{}
    case I.StateVisible{_a0}: Unit{}
    case I.FailedEnvironment{_a0, _a1, _a2}: Unit{}
    case I.Concluded{_a0, _a1, _a2}: Unit{}
    case I.DeliveredEverything{_a0}: Unit{}
    case I.DeliveryInterrupted{_a0}: Unit{}
    case I.ClosedChannel{}: Unit{}
    case I.NextCall{_a0, _a1}: Unit{}

# The initial judgment is needed only in worlds that actually initialize.
def OriginOfMoment(~source: Source.Source, ~seed: Unit -> D.State,
  -c: S.Configuration, -pi: String, moment: C.Moment, +world: Nat) -> Type:
  match moment:
    case C.Initialization{}: JudgmentOfData(source, c, seed(Unit{}), pi, Source.initial(source, world))
    case C.Service{reception}: Unit

def rule1_of_moment(~source: Source.Source, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~history: Nat -> List<&2, H.Record>, ~pi: String,
  moment: C.Moment, +world: Nat, +t: Nat, f: I.Fact,
  canonical: {C.of_moment(c, seed, history, pi, moment, world) == Source.scenario(source, world) : I.Scenario},
  origin: OriginOfMoment(source, seed, c, pi, moment, world),
  fact: Source.of_route(source, C.of_moment(c, seed, history, pi, moment, world), t, f)) ->
  K.Rule1(f, Source.environment(source), Source.artifact(source), C.of_moment(c, seed, history, pi, moment, world), t):
  match moment:
    case C.Initialization{}:
      rule1_initial_data(source, c, world, seed(Unit{}), pi, Source.initial(source, world), t, f, canonical, {==}, origin, fact)
    case C.Service{+reception}:
      rule1_serve_data(source, c, world, H.state(history(world), seed(Unit{})), reception,
        Source.call(source, world), t, f, {==}, fact)

# Lifting: the route is unique and canonical; only target x is transported.
def rule1_of_scenario(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, H.Record>, ~moments: Nat -> C.Moment, ~pi: String,
  x: I.Scenario, +t: Nat, f: I.Fact,
  origins: @m: Nat -> OriginOfMoment(Model.source(base, c, seed, history, moments, pi), seed, c, pi, moments(m), m),
  fact: I.Happens(Source.environment(Model.source(base, c, seed, history, moments, pi)), Source.artifact(Model.source(base, c, seed, history, moments, pi)), x, t, f)) ->
  K.Rule1(f, Source.environment(Model.source(base, c, seed, history, moments, pi)), Source.artifact(Model.source(base, c, seed, history, moments, pi)), x, t):
  match x:
    case I.Initialize{+world, configuration, +s, +proof}:
      match fact:
        case L.Both{name, L.Both{equal, obs}}:
          %Equal.sym(I.Scenario, I.Initialize{world, configuration, s, proof}, C.canonical(c, seed, history, moments, pi, world),
            Equal.trans(I.Scenario, I.Initialize{world, configuration, s, proof}, Source.scenario(Model.source(base, c, seed, history, moments, pi), world),
              C.canonical(c, seed, history, moments, pi, world), equal, Model.scenario_of_model(base, c, seed, history, moments, pi, world))) :
            K.Rule1(f, Source.environment(Model.source(base, c, seed, history, moments, pi)), Source.artifact(Model.source(base, c, seed, history, moments, pi)), _, t)
          rule1_of_moment(Model.source(base, c, seed, history, moments, pi), c, seed, history, pi, moments(world), world, t, f,
            Equal.sym(I.Scenario, Source.scenario(Model.source(base, c, seed, history, moments, pi), world), C.canonical(c, seed, history, moments, pi, world),
              Model.scenario_of_model(base, c, seed, history, moments, pi, world)), origins(world),
            (%Model.scenario_of_model(base, c, seed, history, moments, pi, world) : Source.of_route(Model.source(base, c, seed, history, moments, pi), _, t, f) obs))
    case I.Serve{+world, configuration, +s, +reception}:
      match fact:
        case L.Both{name, L.Both{equal, obs}}:
          %Equal.sym(I.Scenario, I.Serve{world, configuration, s, reception}, C.canonical(c, seed, history, moments, pi, world),
            Equal.trans(I.Scenario, I.Serve{world, configuration, s, reception}, Source.scenario(Model.source(base, c, seed, history, moments, pi), world),
              C.canonical(c, seed, history, moments, pi, world), equal, Model.scenario_of_model(base, c, seed, history, moments, pi, world))) :
            K.Rule1(f, Source.environment(Model.source(base, c, seed, history, moments, pi)), Source.artifact(Model.source(base, c, seed, history, moments, pi)), _, t)
          rule1_of_moment(Model.source(base, c, seed, history, moments, pi), c, seed, history, pi, moments(world), world, t, f,
            Equal.sym(I.Scenario, Source.scenario(Model.source(base, c, seed, history, moments, pi), world), C.canonical(c, seed, history, moments, pi, world),
              Model.scenario_of_model(base, c, seed, history, moments, pi, world)), origins(world),
            (%Model.scenario_of_model(base, c, seed, history, moments, pi, world) : Source.of_route(Model.source(base, c, seed, history, moments, pi), _, t, f) obs))

law law1_of_model:
  for ~base: Source.Source
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~history: Nat -> List<&2, H.Record>
  for ~moments: Nat -> C.Moment
  for ~pi: String
  for origins: @m: Nat -> OriginOfMoment(Model.source(base, c, seed, history, moments, pi), seed, c, pi, moments(m), m)
  K.Law1(Source.environment(Model.source(base, c, seed, history, moments, pi)), Source.artifact(Model.source(base, c, seed, history, moments, pi)))
def law1_of_model(base, c, seed, history, moments, pi, origins):
  x => +t => f => fact => rule1_of_scenario(base, c, seed, history, moments, pi, x, t, f, origins, fact)
