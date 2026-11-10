# Canonical observation of a finite operational event sequence. This is a MODEL
# interpretation: correspondence with all native effects is not a premise here
# and still has to be proved separately. Every ordinary/phase event is retained,
# including explicit unmodelled effects. No claim of a full Contract is made.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/Protocol.bend as P
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../ProtocolService.bend as Q
import ../../SourceService.bend as Source
import ../../HostTransitions.bend as Host
import ../specification/ServiceLaws.bend as E
import ../phases/PreparePhases.bend as V
import ../phases/InvalidationPhases.bend as N
import ./FrameBounds.bend as B

type Change is Data:
  Change{prepared: Bool, mutation: E.Mutation, before: E.Snapshot, after: E.Snapshot}

type AuditEvent is Data:
  Core{prepared: Bool, code: String, frame: Q.Frame}
  BoundCore{prepared: Bool, origin: Source.JudgmentSyntactic, frame: Q.Frame}
  Preparation{event: V.PreparationEvent}
  Invalidation{event: N.InvalidationEvent}
  Selection{snapshot: E.Snapshot}
  Resolution{raw: P.Request, entry: G.Entry, context: D.Context}
  Publication{prepared: Bool, response: S.Response, bytes: List<&2, U32>, before: E.Snapshot, after: E.Snapshot}

type Item is Data:
  Item{world: Nat, selected: D.State, input: X.Reception, event: AuditEvent}

def scenario(~c: S.Configuration, item: Item) -> I.Scenario:
  Item{world, selected, input, event} = item
  I.Serve{world, c, selected, input}

def event(item: Item) -> AuditEvent:
  Item{world, selected, input, event} = item
  event

def phase_change(phase: V.PreparationEvent) -> Maybe<&2, Change>:
  match phase:
    case V.RegistryChanged{entry, before, after}: Some{Change{True{}, E.Register{entry}, before, after}}
    case _: None{}

def invalidation_change(event: N.InvalidationEvent) -> Maybe<&2, Change>:
  match event:
    case N.InvalidationBase{phase}: phase_change(phase)
    case N.RegistryRemoved{handle, before, after}: Some{Change{True{}, E.Invalidate{handle}, before, after}}

def change(event: AuditEvent) -> Maybe<&2, Change>:
  match event:
    case Preparation{phase}: phase_change(phase)
    case Invalidation{event}: invalidation_change(event)
    case Publication{mode, response, bytes, before, after}: Some{Change{mode, E.Publish{response, bytes}, before, after}}
    case _: None{}

def fact(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, event: AuditEvent) -> E.Fact:
  match event:
    case Core{mode, code, frame}:
      E.core_fact(mode, Q.fact_of_frame(c, Source.program(binding, Host.origin(public, code)), frame))
    case BoundCore{mode, origin, frame}:
      E.core_fact(mode, Q.fact_of_frame(c, Source.program(binding, origin), frame))
    case Preparation{phase}: V.fact(c, binding, public, phase)
    case Invalidation{event}: N.fact(c, binding, public, event)
    case Selection{snapshot}: E.Selected{snapshot}
    case Resolution{+raw, +entry, context}:
      E.EntryResolved{raw, entry, H.resolved(raw, entry), context, Source.program(binding, Host.origin(public, G.code(entry)))}
    case Publication{mode, response, bytes, before, after}: E.Mutated{mode, E.Publish{response, bytes}, before, after}

# A real publication has two policy facts at the SAME semantic instant. No
# neighboring artificial event is substituted for this required coupling.
def PublicationFact(event: AuditEvent, -f: E.Fact) -> Type:
  match event:
    case Publication{mode, response, bytes, before, after}: {f == E.core_fact(mode, I.Published{E.database(after)}) : E.Fact}
    case _: Empty

def RelFact(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, -event: AuditEvent, -f: E.Fact) -> Type:
  L.Disjunction<{f == fact(c, binding, public, event) : E.Fact}, PublicationFact(event, f)>

def fact_change(fact: E.Fact) -> Maybe<&2, Change>:
  match fact:
    case E.Mutated{mode, mutation, before, after}: Some{Change{mode, mutation, before, after}}
    case _: None{}

law interpreted_phase_preserves_exact_mutation_data:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for phase: V.PreparationEvent
  {fact_change(V.fact(c, binding, public, phase)) == phase_change(phase) : Maybe<&2, Change>}
def interpreted_phase_preserves_exact_mutation_data(c, binding, public, phase):
  match phase:
    case V.WireReceived{wire}: {==}
    case V.IdentityEstablished{wire, context}: {==}
    case V.Accepted{wire, context}: {==}
    case V.Refuted{wire, context}: {==}
    case V.PrimitiveFailed{stage, identifier, fatal}: {==}
    case V.HandleChosen{handle}: {==}
    case V.ReceiptPrepared{receipt, bytes}: {==}
    case V.ArtifactSealed{entry}: {==}
    case V.RegistryChanged{entry, before, after}: {==}
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: {==}
    case V.ErrorPrepared{status, bytes}: {==}
    case V.ErrorConcluded{status, snapshot, closes}: {==}
    case V.Delivered{bytes}: {==}
    case V.Interrupted{prefix}: {==}
    case V.Closed{}: {==}

law interpreted_event_preserves_exact_mutation_data:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for event: AuditEvent
  {fact_change(fact(c, binding, public, event)) == change(event) : Maybe<&2, Change>}
def interpreted_event_preserves_exact_mutation_data(c, binding, public, event):
  match event:
    case Core{False{}, code, frame}: {==}
    case Core{True{}, code, frame}: {==}
    case BoundCore{False{}, origin, frame}: {==}
    case BoundCore{True{}, origin, frame}: {==}
    case Preparation{phase}: interpreted_phase_preserves_exact_mutation_data(c, binding, public, phase)
    case Invalidation{N.InvalidationBase{phase}}: interpreted_phase_preserves_exact_mutation_data(c, binding, public, phase)
    case Invalidation{N.RegistryRemoved{handle, before, after}}: {==}
    case Selection{snapshot}: {==}
    case Resolution{raw, entry, context}: {==}
    case Publication{mode, response, bytes, before, after}: {==}

def time(index: Nat) -> Nat:
  Succ{Succ{Succ{index}}}

def InitialFact(~c: S.Configuration, ~seed: Unit -> D.State, ~pi: String,
  -instance: String, at: Nat, -f: E.Fact) -> Type:
  match at:
    case 0n: {f == E.Ordinary{I.ProofInitialAccepts{}} : E.Fact}
    case 1n+k:
      match k:
        case 0n: {f == E.Ordinary{I.InstanceStarted{seed(Unit{})}} : E.Fact}
        case 1n+j:
          match j:
            case 0n: {f == E.Boot{E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}} : E.Fact}
            case 1n+rest: Empty

def InitialObserved(~c: S.Configuration, ~seed: Unit -> D.State, ~pi: String,
  -instance: String, -x: I.Scenario, at: Nat, -f: E.Fact) -> Type:
  L.E<{x == I.Initialize{0n, c, seed(Unit{}), pi} : I.Scenario},
    InitialFact(c, seed, pi, instance, at, f)>

def ListedObserved(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  -items: List<&2, Item>, -x: I.Scenario, -at: Nat, -f: E.Fact) -> Type:
  &index: Nat -> &item: Item ->
    L.E<{at == time(index) : Nat},
      L.E<{B.query(Item, items, index) == Some{item} : Maybe<&2, Item>},
        L.E<{x == scenario(c, item) : I.Scenario}, RelFact(c, binding, public, event(item), f)>>>

def environment(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~items: List<&2, Item>, ~instance: String) -> E.Environment:
  E.Environment{Source.identity(binding),
    config => code => program => Source.elaboration(binding, config, code, program),
    config => text => target => Source.derivation(binding, config, text, target),
    x => Source.processable(binding, x),
    k => x => at => stage => id => fatal => Source.failure(binding, k, x, at, stage, id, fatal),
    k => x => at => Source.failure_delivery(binding, k, x, at), artifacts,
    world => 0n,
    k => x => at => f => L.E<{k == Source.artifact(binding) : String},
      L.Disjunction<InitialObserved(c, seed, pi, instance, x, at, f), ListedObserved(c, binding, public, items, x, at, f)>>}

law operational_observer_preserves_the_same_external_processable:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~items: List<&2, Item>
  for ~instance: String
  for -x: I.Scenario
  {E.Processable(environment(binding, public, c, seed, pi, artifacts, items, instance), x) == Source.processable(binding, x) : Type}
def operational_observer_preserves_the_same_external_processable(binding, public, c, seed, pi, artifacts, items, instance, x):
  {==}
