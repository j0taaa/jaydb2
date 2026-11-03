# Composition of the generated protocol's eight laws. Premises below are
# primitive source/tool/IO contracts, never LawN or RuleN.
# Their correspondence with Rust/Node/C remains the explicit trusted
# boundary; no official compiler contract is proved here.
import Base
import ../contract/Data.bend as D
import ../contract/LAWS.bend as K
import ../contract/Logic.bend as L
import ../contract/Resources.bend as X
import ../contract/Semantics.bend as S
import ./SourceService.bend as Source
import ./ModelService.bend as Model
import ./ScenariosService.bend as Scenarios
import ./HistoryService.bend as History
import ./Law1Service.bend as One
import ./Law2Service.bend as Two
import ./Law34Service.bend as Admission
import ./Law5Service.bend as Five
import ./Law6Service.bend as Six
import ./Law7Service.bend as Seven
import ./Law8Service.bend as Eight
import ./PublicationService.bend as Publication
import ./ChannelService.bend as Channel
import ./VisibilityService.bend as Vis

# Each family is exposed in its own module: closed initial judgment; Codec/copy
# primitive results; certified execution and history; IO effects;
# primitive return under external Processable, without physical deadlines.
def Initial(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String) -> Type:
  @m: Nat -> One.OriginOfMoment(Model.source(base, c, seed, history, moment, pi), seed, c, pi, moment(m), m)
def Observations(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String) -> Type:
  @m: Nat -> Two.OriginOfModel(base, c, seed, history, moment, pi, m)
def SourcesExecution(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String) -> Type:
  @m: Nat -> Publication.OriginOfMoment(Model.source(base, c, seed, history, moment, pi), c, seed, history, m, moment(m))
def IOOfMoment(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, +world: Nat, moment: Scenarios.Moment) -> Type:
  match moment:
    case Scenarios.Initialization{}: Channel.FailuresReal(source, Source.scenario(source, world), Vis.frames_initial(source, c, seed(Unit{}), Source.initial(source, world)))
    case Scenarios.Service{+rx}: Seven.OriginOfCall7(source, c, world, History.state(history(world), seed(Unit{})), rx, Source.call(source, world))

def Communication(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String) -> Type:
  @m: Nat -> IOOfMoment(Model.source(base, c, seed, history, moment, pi), c, seed, history, m, moment(m))

def Premises(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String) -> Type:
  L.E<Initial(base, c, seed, history, moment, pi),
    L.E<Observations(base, c, seed, history, moment, pi),
      L.E<SourcesExecution(base, c, seed, history, moment, pi),
        L.E<Communication(base, c, seed, history, moment, pi),
          Eight.AvailabilityOfModel(base, c, seed, history, moment, pi)>>>>

# Linear projections: every proof queries a reopening of the same source.
def initial(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  p: Premises(base, c, seed, history, moment, pi)) -> Initial(base, c, seed, history, moment, pi):
  match p:
    case L.Both{h, rest}: h

def observations(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  p: Premises(base, c, seed, history, moment, pi)) -> Observations(base, c, seed, history, moment, pi):
  match p:
    case L.Both{initial, L.Both{h, rest}}: h

def sources_execution(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  p: Premises(base, c, seed, history, moment, pi)) -> SourcesExecution(base, c, seed, history, moment, pi):
  match p:
    case L.Both{initial, L.Both{obs, L.Both{h, rest}}}: h

def io_of_moment(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, +world: Nat, moment: Scenarios.Moment,
  source_execution: Publication.OriginOfMoment(source, c, seed, history, world, moment),
  io: IOOfMoment(source, c, seed, history, world, moment)) -> Seven.OriginOfMoment7(source, c, seed, history, world, moment):
  match moment:
    case Scenarios.Initialization{}: io
    case Scenarios.Service{rx}:
      match source_execution:
        case L.Both{real, judgment}: L.Both{real, io}

def communication(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  p: Premises(base, c, seed, history, moment, pi)) ->
  @m: Nat -> Seven.OriginOfMoment7(Model.source(base, c, seed, history, moment, pi), c, seed, history, m, moment(m)):
  match p:
    case L.Both{initial, L.Both{obs, L.Both{exec, L.Both{io, rest}}}}:
      +m => io_of_moment(Model.source(base, c, seed, history, moment, pi), c, seed, history, m, moment(m), exec(m), io(m))

def availability(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  p: Premises(base, c, seed, history, moment, pi)) -> Eight.AvailabilityOfModel(base, c, seed, history, moment, pi):
  match p:
    case L.Both{initial, L.Both{obs, L.Both{exec, L.Both{io, h}}}}: h

# Laws 3/4/5 reuse the richer origin already required for Law 6.
def admission_of_call(~source: Source.Source, ~c: S.Configuration, +s: D.State, +rx: X.Reception,
  data: Source.CallData, real: Five.CallReal(source, c, s, rx, data), judgment: Publication.JudgmentOfCall(source, c, rx, data)) -> Admission.OriginCall(source, c, s, rx, data):
  match data:
    case Source.CallData{cf, origin, pf, tf, state, tools, micro}: L.Both{real, judgment}

def admission_of_moment(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, +world: Nat, moment: Scenarios.Moment,
  origin: Publication.OriginOfMoment(source, c, seed, history, world, moment)) -> Admission.OriginOfMoment(source, c, seed, history, world, moment):
  match moment:
    case Scenarios.Initialization{}: Unit{}
    case Scenarios.Service{+rx}:
      match origin:
        case L.Both{L.Both{cfg, L.Both{seed_valid, L.Both{histories, real}}}, judgment}:
          admission_of_call(source, c, History.state(history(world), seed(Unit{})), rx, Source.call(source, world), real, judgment)

def execution_of_moment(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, +world: Nat, moment: Scenarios.Moment,
  origin: Publication.OriginOfMoment(source, c, seed, history, world, moment)) -> Five.OriginOfMoment(source, c, seed, history, world, moment):
  match moment:
    case Scenarios.Initialization{}: Unit{}
    case Scenarios.Service{rx}:
      match origin:
        case L.Both{real, judgment}: real

def admissions(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  sources: SourcesExecution(base, c, seed, history, moment, pi)) ->
  @m: Nat -> Admission.OriginOfMoment(Model.source(base, c, seed, history, moment, pi), c, seed, history, m, moment(m)):
  +m => admission_of_moment(Model.source(base, c, seed, history, moment, pi), c, seed, history, m, moment(m), sources(m))

def executions(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  sources: SourcesExecution(base, c, seed, history, moment, pi)) ->
  @m: Nat -> Five.OriginOfMoment(Model.source(base, c, seed, history, moment, pi), c, seed, history, m, moment(m)):
  +m => execution_of_moment(Model.source(base, c, seed, history, moment, pi), c, seed, history, m, moment(m), sources(m))

# ~reopen denotes a CLOSED primitive-fact declaration. Each call
# supplies a fresh value; captured Type programs and proofs are not copied.
def Reopened(-P: Type) -> Type:
  L.E<P, L.E<P, L.E<P, L.E<P, L.E<P, L.E<P, L.E<P, P>>>>>>>

def reopen_sources(~P: Type, ~reopen: Unit -> P, -Q: Type, same: {P == Q : Type}) -> Reopened(Q):
  %same : Reopened(_)
  L.Both{reopen(Unit{}), L.Both{reopen(Unit{}), L.Both{reopen(Unit{}), L.Both{reopen(Unit{}), L.Both{reopen(Unit{}), L.Both{reopen(Unit{}), L.Both{reopen(Unit{}), reopen(Unit{})}}}}}}}

def compose(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  sources: Reopened(Premises(base, c, seed, history, moment, pi))) ->
  K.Contract(Source.environment(Model.source(base, c, seed, history, moment, pi)), Source.artifact(Model.source(base, c, seed, history, moment, pi))):
  match sources:
    case L.Both{p1, L.Both{p2, L.Both{p3, L.Both{p4, L.Both{p5, L.Both{p6, L.Both{p7, p8}}}}}}}:
      L.Both{One.law1_of_model(base, c, seed, history, moment, pi, initial(base, c, seed, history, moment, pi, p1)),
        L.Both{Two.law2_of_model(base, c, seed, history, moment, pi, observations(base, c, seed, history, moment, pi, p2)),
          L.Both{Admission.law3_of_model(base, c, seed, history, moment, pi, admissions(base, c, seed, history, moment, pi, sources_execution(base, c, seed, history, moment, pi, p3))),
            L.Both{Admission.law4_of_model(base, c, seed, history, moment, pi, admissions(base, c, seed, history, moment, pi, sources_execution(base, c, seed, history, moment, pi, p4))),
              L.Both{Five.law5_of_model(base, c, seed, history, moment, pi, executions(base, c, seed, history, moment, pi, sources_execution(base, c, seed, history, moment, pi, p5))),
                L.Both{Six.law6_of_model(base, c, seed, history, moment, pi, sources_execution(base, c, seed, history, moment, pi, p6)),
                  L.Both{Seven.law7_of_model(base, c, seed, history, moment, pi, communication(base, c, seed, history, moment, pi, p7)),
                    Eight.law8_of_model(base, c, seed, history, moment, pi, availability(base, c, seed, history, moment, pi, p8))}}}}}}}

# The target is EXACTLY LAWS.Contract, not a renamed smaller record.
law contract_of_service:
  for ~base: Source.Source
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~history: Nat -> List<&2, History.Record>
  for ~moment: Nat -> Scenarios.Moment
  for ~pi: String
  for ~P: Type
  for ~reopen: Unit -> P
  for same: {P == Premises(base, c, seed, history, moment, pi) : Type}
  K.Contract(Source.environment(Model.source(base, c, seed, history, moment, pi)), Source.artifact(Model.source(base, c, seed, history, moment, pi)))
def contract_of_service(base, c, seed, history, moment, pi, P, reopen, same):
  compose(base, c, seed, history, moment, pi, reopen_sources(P, reopen, Premises(base, c, seed, history, moment, pi), same))
