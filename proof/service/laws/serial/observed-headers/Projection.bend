# Recover actual complete Items/RelFacts for either header. Initialization and
# real publication cofacts cannot impersonate headers; nothing is filtered
# from the underlying observer and no global Plain premise is supplied.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/Semantics.bend as S
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/serial/Engine.bend as Engine
import ../ObservationLocation.bend as Locate
import ../header/History.bend as History
import ./HeaderData.bend as Header


def cofact_void(+event: O.AuditEvent, -f: E.Fact, relation: O.PublicationFact(event, f)) -> {Header.fact(f) == Header.Void{} : Header.View}:
  match event:
    case O.Publication{+mode, response, bytes, before, +after}:
      Equal.trans(Header.View, Header.fact(f), Header.fact(E.core_fact(mode, I.Published{E.database(after)})), Header.Void{},
        Equal.cong(E.Fact, Header.View, Header.fact, f, E.core_fact(mode, I.Published{E.database(after)}), relation), Header.core_fact_view(mode, I.Published{E.database(after)}))
    case O.Core{mode, code, frame}: L.ex_false({Header.fact(f) == Header.Void{} : Header.View}, relation)
    case O.BoundCore{mode, origin, frame}: L.ex_false({Header.fact(f) == Header.Void{} : Header.View}, relation)
    case O.Preparation{phase}: L.ex_false({Header.fact(f) == Header.Void{} : Header.View}, relation)
    case O.Invalidation{phase}: L.ex_false({Header.fact(f) == Header.Void{} : Header.View}, relation)
    case O.Selection{snapshot}: L.ex_false({Header.fact(f) == Header.Void{} : Header.View}, relation)
    case O.Resolution{raw, entry, context}: L.ex_false({Header.fact(f) == Header.Void{} : Header.View}, relation)


def actual_event_view(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +event: O.AuditEvent, -f: E.Fact, relevant: Header.Relevant(Header.fact(f)), relation: O.RelFact(c, binding, public, event, f)) ->
  {Header.event(event) == Header.fact(f) : Header.View}:
  match relation:
    case L.Left{same}:
      Equal.trans(Header.View, Header.event(event), Header.fact(O.fact(c, binding, public, event)), Header.fact(f),
        Equal.sym(Header.View, Header.fact(O.fact(c, binding, public, event)), Header.event(event), Header.canonical_interpretation(c, binding, public, event)),
        Equal.sym(Header.View, Header.fact(f), Header.fact(O.fact(c, binding, public, event)), Equal.cong(E.Fact, Header.View, Header.fact, f, O.fact(c, binding, public, event), same)))
    case L.Right{cofact}:
      L.ex_false({Header.event(event) == Header.fact(f) : Header.View}, Header.irrelevant(Header.fact(f), relevant, cofact_void(event, f, cofact)))


def initial_void(~c: S.Configuration, ~seed: Unit -> D.State, ~pi: String, -instance: String,
  at: Nat, -f: E.Fact, initial: O.InitialFact(c, seed, pi, instance, at, f)) -> {Header.fact(f) == Header.Void{} : Header.View}:
  match at:
    case 0n: Equal.cong(E.Fact, Header.View, Header.fact, f, E.Ordinary{I.ProofInitialAccepts{}}, initial)
    case 1n+k:
      match k:
        case 0n: Equal.cong(E.Fact, Header.View, Header.fact, f, E.Ordinary{I.InstanceStarted{seed(Unit{})}}, initial)
        case 1n+j:
          match j:
            case 0n: Equal.cong(E.Fact, Header.View, Header.fact, f, E.Boot{E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}}, initial)
            case 1n+rest: L.ex_false({Header.fact(f) == Header.Void{} : Header.View}, initial)


def listed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +k: String, -x: I.Scenario, +at: Nat, -f: E.Fact, relevant: Header.Relevant(Header.fact(f)),
  observed: E.observes(History.environment(c, binding, public, script, seed, pi, artifacts, instance), k, x, at, f)) ->
  L.E<{k == Source.artifact(binding) : String}, O.ListedObserved(c, binding, public, History.items(c, binding, public, script, seed, instance), x, at, f)>:
  match observed:
    case L.Both{artifact, L.Left{L.Both{scenario, initial}}}:
      L.ex_false(L.E<{k == Source.artifact(binding) : String}, O.ListedObserved(c, binding, public, History.items(c, binding, public, script, seed, instance), x, at, f)>,
        Header.irrelevant(Header.fact(f), relevant, initial_void(c, seed, pi, instance, at, f, initial)))
    case L.Both{artifact, L.Right{actual}}: L.Both{artifact, actual}


def from_listed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  -k: String, -x: I.Scenario, +at: Nat, -f: E.Fact,
  actual: L.E<{k == Source.artifact(binding) : String}, O.ListedObserved(c, binding, public, History.items(c, binding, public, script, seed, instance), x, at, f)>) ->
  L.E<{k == Source.artifact(binding) : String}, Locate.Located(c, binding, public, script, History.boot(seed, instance), x, at, f)>:
  match actual:
    case L.Both{artifact, entry}:
      L.Both{artifact, Locate.locate_listed(c, binding, public, script, History.boot(seed, instance), x, at, f, entry)}


law every_actual_header_observation_recovers_its_exact_global_item_block_and_unaltered_cofact_relation:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~script: List<&2, Engine.Job>
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~instance: String
  for +k: String
  for -x: I.Scenario
  for +at: Nat
  for -f: E.Fact
  for relevant: Header.Relevant(Header.fact(f))
  for observed: E.observes(History.environment(c, binding, public, script, seed, pi, artifacts, instance), k, x, at, f)
  L.E<{k == Source.artifact(binding) : String}, Locate.Located(c, binding, public, script, History.boot(seed, instance), x, at, f)>
def every_actual_header_observation_recovers_its_exact_global_item_block_and_unaltered_cofact_relation(c, binding, public, script, seed, pi, artifacts, instance, k, x, at, f, relevant, observed):
  from_listed(c, binding, public, script, seed, pi, artifacts, instance, k, x, at, f,
    listed(c, binding, public, script, seed, pi, artifacts, instance, k, x, at, f, relevant, observed))
