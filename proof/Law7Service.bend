# Responses and IO of the same generated protocol, under explicit primitive contracts.
import Base
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../contract/Interface.bend as I
import ../contract/Semantics.bend as S
import ../contract/Resources.bend as X
import ../contract/LAWS.bend as K
import ./SourceService.bend as Source
import ./RoutesService.bend as Route
import ./ProtocolService.bend as Q
import ./ConclusionService.bend as C
import ./ChannelService.bend as Channel
import ./ClosuresService.bend as Closures
import ./LinkageService.bend as Lig
import ./VisibilityService.bend as Vis
import ./InputService.bend as Copy
import ./Law2Service.bend as Two
import ./Law5Service.bend as Five
import ./HistoryService.bend as History
import ./ScenariosService.bend as Scenarios
import ./ModelService.bend as Model
import ../contract/Requirements.bend as Req
import ./Foundations.bend as F
import ./PhasesService.bend as Phases
import ./Law8Service.bend as Eight
import ./Law6Service.bend as Six
import ../src/ConfigurationCheck.bend as Config

# Origin of bytes, technical results and actual POSIX effects.
# No field supplies Rule7, ResponseJustified or a database conclusion.
def OriginOfCall7(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State,
  +rx: X.Reception, +data: Source.CallData) -> Type:
  match data:
    case Source.CallData{cf, pf, cert, terminates, +be, +tools, +micro}:
      L.E<Copy.StateCopied(c, s, be),
        L.E<Copy.BodyCopied(c, rx),
          L.E<Two.OctetsReceived(X.decide_reception(c, rx)),
            L.E<C.FramingReached(Route.preprocessing(tools), X.decide_reception(c, rx)),
              L.E<C.WritesAvailable(source, c, world, s, rx, Closures.closure_of_branch(micro, s, Route.decide(c, rx, be, tools))),
                L.E<C.PrefixesOfClosure(Closures.closure_of_branch(micro, s, Route.decide(c, rx, be, tools))),
                  L.E<Channel.FailuresReal(source, I.Serve{world, c, s, rx}, Route.generate(c, rx, be, s, tools, micro)),
                    Channel.FailuresOfDeliveryReal(source, I.Serve{world, c, s, rx}, Route.generate(c, rx, be, s, tools, micro))>>>>>>>

# Configuration/seed/history/execution share the same origin as Law5/Pub6.
def OriginOfMoment7(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, +world: Nat, moment: Scenarios.Moment) -> Type:
  match moment:
    case Scenarios.Initialization{}:
      Channel.FailuresReal(source, Source.scenario(source, world), Vis.frames_initial(source, c, seed(Unit{}), Source.initial(source, world)))
    case Scenarios.Service{+rx}:
      L.E<Five.OriginOfMoment(source, c, seed, history, world, Scenarios.Service{rx}),
        OriginOfCall7(source, c, world, History.state(history(world), seed(Unit{})), rx, Source.call(source, world))>

def preparation_initial_excluded(~source: Source.Source, ~c: S.Configuration, +s: D.State,
  data: Source.InitialData, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  query_result: {Q.query(Vis.frames_initial(source, c, s, data), t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) -> Empty:
  match data:
    case Source.InitialData{cf, sf, pf, j, result, micro}:
      Closures.initialization_without_preparation(micro, s, j, result, Config.is_valid(c, Source.identity(source)))(r, bs, t, query_result)

def deliveries_initial_absent(~source: Source.Source, ~c: S.Configuration, +s: D.State, data: Source.InitialData) ->
  L.E<{Phases.absent(Phases.Complete{}, Vis.frames_initial(source, c, s, data)) == True{} : Bool},
    {Phases.absent(Phases.Interrupted{}, Vis.frames_initial(source, c, s, data)) == True{} : Bool}>:
  match data:
    case Source.InitialData{cf, sf, pf, +j, +result, +micro}:
      L.and_right({Phases.absent(Phases.Conclusion{}, Route.generate_result_initial(c, Source.identity(source), s, j, result, micro)) == True{} : Bool},
        L.E<{Phases.absent(Phases.Complete{}, Route.generate_result_initial(c, Source.identity(source), s, j, result, micro)) == True{} : Bool},
          {Phases.absent(Phases.Interrupted{}, Route.generate_result_initial(c, Source.identity(source), s, j, result, micro)) == True{} : Bool}>,
        Closures.initialization_without_conclusion_delivery(micro, s, j, result, Config.is_valid(c, Source.identity(source))))

def failure_initial_combined_origin(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +pi: String,
  +t: Nat, +stage: X.Stage, +id: String, +fatal: Bool,
  real: Channel.FailuresReal(source, Source.scenario(source, world), Vis.frames_initial(source, c, s, Source.initial(source, world))),
  literal: L.E<{Source.artifact(source) == Source.artifact(source) : String},
    L.E<{I.Initialize{world, c, s, pi} == Source.scenario(source, world) : I.Scenario},
      Source.of_route(source, I.Initialize{world, c, s, pi}, t, I.FailedEnvironment{stage, id, fatal})>>) ->
  I.FailureReal(Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t, stage, id, fatal):
  match literal:
    case L.Both{name, L.Both{canonical, raw}}:
      %Equal.sym(I.Scenario, I.Initialize{world, c, s, pi}, Source.scenario(source, world), canonical) :
        I.FailureReal(Source.environment(source), Source.artifact(source), _, t, stage, id, fatal)
      real(t, stage, id, fatal, Channel.extract_initial_data(source, c, s, Source.initial(source, world), t, I.FailedEnvironment{stage, id, fatal}, Unit{}, raw))

def rule7_initial(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +pi: String, +t: Nat, f: I.Fact,
  real: Channel.FailuresReal(source, Source.scenario(source, world), Vis.frames_initial(source, c, s, Source.initial(source, world))),
  fact: I.Happens(Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t, f)) ->
  K.Rule7(f, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t):
  match f:
    case I.Prepared{+r, +bs}:
      L.ex_false(K.Rule7(I.Prepared{r, bs}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t),
        preparation_initial_excluded(source, c, s, Source.initial(source, world), t, r, bs,
          Channel.extract_initial(source, c, world, s, pi, t, I.Prepared{r, bs}, Unit{}, Source.eliminate_fact_literal(source, Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.Prepared{r, bs}, fact))))
    case I.Concluded{+r, +w, +closes}:
      L.ex_false(K.Rule7(I.Concluded{r, w, closes}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t),
        Six.conclusion_initial_and_impossible(source, c, world, s, pi, t, r, w, closes, fact))
    case I.DeliveredEverything{+bs}:
      L.ex_false(K.Rule7(I.DeliveredEverything{bs}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t),
        Phases.absent_excludes_query(Phases.Complete{}, Vis.frames_initial(source, c, s, Source.initial(source, world)), t, Q.Delivered{bs},
          L.and_left({Phases.absent(Phases.Complete{}, Vis.frames_initial(source, c, s, Source.initial(source, world))) == True{} : Bool},
            {Phases.absent(Phases.Interrupted{}, Vis.frames_initial(source, c, s, Source.initial(source, world))) == True{} : Bool},
            deliveries_initial_absent(source, c, s, Source.initial(source, world))), {==},
          Channel.extract_initial(source, c, world, s, pi, t, I.DeliveredEverything{bs}, Unit{}, Source.eliminate_fact_literal(source, Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.DeliveredEverything{bs}, fact))))
    case I.DeliveryInterrupted{+bs}:
      L.ex_false(K.Rule7(I.DeliveryInterrupted{bs}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t),
        Phases.absent_excludes_query(Phases.Interrupted{}, Vis.frames_initial(source, c, s, Source.initial(source, world)), t, Q.Interrupted{bs},
          L.and_right({Phases.absent(Phases.Complete{}, Vis.frames_initial(source, c, s, Source.initial(source, world))) == True{} : Bool},
            {Phases.absent(Phases.Interrupted{}, Vis.frames_initial(source, c, s, Source.initial(source, world))) == True{} : Bool},
            deliveries_initial_absent(source, c, s, Source.initial(source, world))), {==},
          Channel.extract_initial(source, c, world, s, pi, t, I.DeliveryInterrupted{bs}, Unit{}, Source.eliminate_fact_literal(source, Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.DeliveryInterrupted{bs}, fact))))
    case I.FailedEnvironment{+stage, +id, +fatal}:
      failure_initial_combined_origin(source, c, world, s, pi, t, stage, id, fatal, real,
        Source.eliminate_fact_literal(source, Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.FailedEnvironment{stage, id, fatal}, fact))
    case I.ClosedChannel{}:
      L.ex_false(K.Rule7(I.ClosedChannel{}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t),
        Channel.closure_of_initialization_impossible(source, c, world, s, pi, t, fact))
    case I.ConfigurationInUse{v}: Unit{}
    case I.InspectionNotModeled{v}: Unit{}
    case I.EffectNotModeled{v}: Unit{}
    case I.InstanceStarted{v}: Unit{}
    case I.InitializationRefused{v}: Unit{}
    case I.ProofInitialAccepts{}: Unit{}
    case I.Encoded{a, b}: Unit{}
    case I.Decoded{a, b}: Unit{}
    case I.Stored{a, b, d}: Unit{}
    case I.Operated{a, b, d, e}: Unit{}
    case I.CheckedLength{a, b}: Unit{}
    case I.AllocatedField{a, b}: Unit{}
    case I.ReadBody{a, b, d}: Unit{}
    case I.ReceivedRequest{a}: Unit{}
    case I.Authenticated{a, b}: Unit{}
    case I.CertificateAccepted{a, b, p}: Unit{}
    case I.CertificateRejected{a, b}: Unit{}
    case I.ProgramStarted{a, b, p}: Unit{}
    case I.Evaluated{a, b, p, v}: Unit{}
    case I.Published{a}: Unit{}
    case I.StateVisible{a}: Unit{}
    case I.NextCall{a, b}: Unit{}

# Opens metadata ONCE; getters preserve the same fact tuple.
def IOOpen(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State,
  +rx: X.Reception, +data: Source.CallData) -> Type:
  L.E<C.StateOfCall(c, s, data),
    L.E<Copy.BodyCopied(c, rx),
      L.E<Two.OctetsReceived(X.decide_reception(c, rx)),
        L.E<C.ReachedPacket(c, rx, data),
          L.E<C.WritesAvailable(source, c, world, s, rx, Closures.closure_of_branch(Lig.micro_of_data(data), s, Lig.branch_of_data(c, rx, data))),
            L.E<C.PrefixesOfClosure(Closures.closure_of_branch(Lig.micro_of_data(data), s, Lig.branch_of_data(c, rx, data))),
              L.E<Channel.FailuresReal(source, I.Serve{world, c, s, rx}, Vis.frames_call(c, s, rx, data)),
                Channel.FailuresOfDeliveryReal(source, I.Serve{world, c, s, rx}, Vis.frames_call(c, s, rx, data))>>>>>>>

def open_io(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State,
  +rx: X.Reception, data: Source.CallData, io: OriginOfCall7(source, c, world, s, rx, data)) -> IOOpen(source, c, world, s, rx, data):
  match data:
    case Source.CallData{cf, pf, cert, terminates, be, tools, micro}: io

# The fact itself already contains equality with the canonical scenario.
def closure7(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State,
  +rx: X.Reception, +t: Nat,
  origin: L.E<{Source.artifact(source) == Source.artifact(source) : String},
    L.E<{I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario}, Source.of_route(source, I.Serve{world, c, s, rx}, t, I.ClosedChannel{})>>) ->
  K.Rule7(I.ClosedChannel{}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t):
  match origin:
    case L.Both{name, L.Both{canonical, obs}}:
      Channel.close_of_cause(source, c, world, s, rx, t, canonical,
        Channel.causes_semantics_of_call(c, world, s, rx, Source.call(source, world))(t,
          Lig.frame_of_observation(source, c, s, rx, Source.call(source, world), t, I.ClosedChannel{}, Unit{}, obs)))

def rule7_service_open(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +t: Nat, cfg: {Req.configuration_is_valid(c) == True{} : Bool}, structure: {D.structure(S.schema(c), s) == True{} : Bool},
  real: Five.CallReal(source, c, s, rx, Source.call(source, world)),
  io: IOOpen(source, c, world, s, rx, Source.call(source, world)), f: I.Fact,
  fact: I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t, f)) ->
  K.Rule7(f, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t):
  match io:
    case L.Both{state, L.Both{body, L.Both{octets, L.Both{reached, L.Both{writes, L.Both{prefixes, L.Both{failures, failures_delivery}}}}}}}:
      match f:
        case I.Prepared{+r, +bs}: C.preparation_of_source_obeys_rule7(source, c, world, s, rx, t, r, bs, real, state, body, octets, structure, cfg, fact)
        case I.Concluded{+r, +w, +closes}: C.conclusion_of_call_obeys_rule7(source, c, world, s, rx, t, r, w, closes, reached, writes, fact)
        case I.DeliveredEverything{+bs}: C.delivery_of_call_obeys_rule7(source, c, world, s, rx, t, C.CompleteObserved{bs}, prefixes, failures_delivery, fact)
        case I.DeliveryInterrupted{+bs}: C.delivery_of_call_obeys_rule7(source, c, world, s, rx, t, C.PartialObserved{bs}, prefixes, failures_delivery, fact)
        case I.FailedEnvironment{+stage, +id, +fatal}: Channel.failure_real_of_call(source, c, world, s, rx, t, stage, id, fatal, failures, fact)
        case I.ClosedChannel{}: closure7(source, c, world, s, rx, t, Source.eliminate_fact_literal(source, Source.artifact(source), I.Serve{world, c, s, rx}, t, I.ClosedChannel{}, fact))
        case I.ConfigurationInUse{a0}: Unit{}
        case I.InspectionNotModeled{a0}: Unit{}
        case I.EffectNotModeled{a0}: Unit{}
        case I.InstanceStarted{a0}: Unit{}
        case I.InitializationRefused{a0}: Unit{}
        case I.ProofInitialAccepts{}: Unit{}
        case I.Encoded{a0, a1}: Unit{}
        case I.Decoded{a0, a1}: Unit{}
        case I.Stored{a0, a1, a2}: Unit{}
        case I.Operated{a0, a1, a2, a3}: Unit{}
        case I.CheckedLength{a0, a1}: Unit{}
        case I.AllocatedField{a0, a1}: Unit{}
        case I.ReadBody{a0, a1, a2}: Unit{}
        case I.ReceivedRequest{a0}: Unit{}
        case I.Authenticated{a0, a1}: Unit{}
        case I.CertificateAccepted{a0, a1, a2}: Unit{}
        case I.CertificateRejected{a0, a1}: Unit{}
        case I.ProgramStarted{a0, a1, a2}: Unit{}
        case I.Evaluated{a0, a1, a2, a3}: Unit{}
        case I.Published{a0}: Unit{}
        case I.StateVisible{a0}: Unit{}
        case I.NextCall{a0, a1}: Unit{}

def rule7_service(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, +world: Nat, +rx: X.Reception, +t: Nat, f: I.Fact,
  origin: OriginOfMoment7(source, c, seed, history, world, Scenarios.Service{rx}),
  fact: I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, History.state(history(world), seed(Unit{})), rx}, t, f)) ->
  K.Rule7(f, Source.environment(source), Source.artifact(source), I.Serve{world, c, History.state(history(world), seed(Unit{})), rx}, t):
  match origin:
    case L.Both{L.Both{cfg, L.Both{initial, L.Both{sources, real}}}, io}:
      F.combined_pair(K.Rule7(f, Source.environment(source), Source.artifact(source), I.Serve{world, c, History.state(history(world), seed(Unit{})), rx}, t),
        {Req.configuration_is_valid(c) == True{} : Bool}, {S.environment(c) == I.identity(Source.environment(source)) : String}, cfg,
        configured => identity => F.combined_pair(K.Rule7(f, Source.environment(source), Source.artifact(source), I.Serve{world, c, History.state(history(world), seed(Unit{})), rx}, t),
          {Req.structure(c, History.state(history(world), seed(Unit{}))) == True{} : Bool}, S.Satisfies(c, S.Stable{History.state(history(world), seed(Unit{}))}),
          History.history_preserves_validity(c, history(world), seed(Unit{}), initial, sources),
          structure => laws => rule7_service_open(source, c, world, History.state(history(world), seed(Unit{})), rx, t, configured,
            Eight.structure_of_state(c, History.state(history(world), seed(Unit{})), structure), real,
            open_io(source, c, world, History.state(history(world), seed(Unit{})), rx, Source.call(source, world), io), f, fact)))

def rule7_in_moment(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~pi: String, +world: Nat, +moment: Scenarios.Moment,
  +t: Nat, f: I.Fact, origin: OriginOfMoment7(source, c, seed, history, world, moment),
  obs: I.Happens(Source.environment(source), Source.artifact(source), Scenarios.of_moment(c, seed, history, pi, moment, world), t, f)) ->
  K.Rule7(f, Source.environment(source), Source.artifact(source), Scenarios.of_moment(c, seed, history, pi, moment, world), t):
  match moment:
    case Scenarios.Initialization{}: rule7_initial(source, c, world, seed(Unit{}), pi, t, f, origin, obs)
    case Scenarios.Service{r}: rule7_service(source, c, seed, history, world, r, t, f, origin, obs)

def rule7_of_origin(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  -x: I.Scenario, +world: Nat, +t: Nat, f: I.Fact,
  origin: OriginOfMoment7(Model.source(base, c, seed, history, moment, pi), c, seed, history, world, moment(world)),
  observed: L.E<{Source.artifact(Model.source(base, c, seed, history, moment, pi)) == Source.artifact(Model.source(base, c, seed, history, moment, pi)) : String},
    L.E<{x == Source.scenario(Model.source(base, c, seed, history, moment, pi), world) : I.Scenario},
      Source.of_route(Model.source(base, c, seed, history, moment, pi), Source.scenario(Model.source(base, c, seed, history, moment, pi), world), t, f)>>) ->
  K.Rule7(f, Source.environment(Model.source(base, c, seed, history, moment, pi)), Source.artifact(Model.source(base, c, seed, history, moment, pi)), x, t):
  match observed:
    case L.Both{name, L.Both{equal, raw}}:
      %Equal.sym(I.Scenario, x, Scenarios.canonical(c, seed, history, moment, pi, world),
        Equal.trans(I.Scenario, x, Source.scenario(Model.source(base, c, seed, history, moment, pi), world),
          Scenarios.canonical(c, seed, history, moment, pi, world), equal, Model.scenario_of_model(base, c, seed, history, moment, pi, world))) :
        K.Rule7(f, Source.environment(Model.source(base, c, seed, history, moment, pi)), Source.artifact(Model.source(base, c, seed, history, moment, pi)), _, t)
      rule7_in_moment(Model.source(base, c, seed, history, moment, pi), c, seed, history, pi, world, moment(world), t, f, origin,
        Six.fact_in_moment(Model.source(base, c, seed, history, moment, pi), c, seed, history, pi, world, moment(world), t, f,
          Model.scenario_of_model(base, c, seed, history, moment, pi, world), raw))

def law7_of_scenario(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  origins: @m: Nat -> OriginOfMoment7(Model.source(base, c, seed, history, moment, pi), c, seed, history, m, moment(m)),
  x: I.Scenario, +t: Nat, f: I.Fact,
  observed: I.Happens(Source.environment(Model.source(base, c, seed, history, moment, pi)), Source.artifact(Model.source(base, c, seed, history, moment, pi)), x, t, f)) ->
  K.Rule7(f, Source.environment(Model.source(base, c, seed, history, moment, pi)), Source.artifact(Model.source(base, c, seed, history, moment, pi)), x, t):
  match x:
    case I.Initialize{+m, original, +s, +proof}:
      rule7_of_origin(base, c, seed, history, moment, pi, I.Initialize{m, original, s, proof}, m, t, f, origins(m),
        Source.eliminate_fact(Model.source(base, c, seed, history, moment, pi), Source.artifact(Model.source(base, c, seed, history, moment, pi)), I.Initialize{m, original, s, proof}, t, f, observed))
    case I.Serve{+m, original, +s, +reception}:
      rule7_of_origin(base, c, seed, history, moment, pi, I.Serve{m, original, s, reception}, m, t, f, origins(m),
        Source.eliminate_fact(Model.source(base, c, seed, history, moment, pi), Source.artifact(Model.source(base, c, seed, history, moment, pi)), I.Serve{m, original, s, reception}, t, f, observed))

def law7_of_model(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  origins: @m: Nat -> OriginOfMoment7(Model.source(base, c, seed, history, moment, pi), c, seed, history, m, moment(m))) ->
  K.Law7(Source.environment(Model.source(base, c, seed, history, moment, pi)), Source.artifact(Model.source(base, c, seed, history, moment, pi))):
  x => +t => f => observed => law7_of_scenario(base, c, seed, history, moment, pi, origins, x, t, f, observed)
