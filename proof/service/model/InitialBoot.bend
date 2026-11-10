# Complete Boot Rule1 over the unfiltered operational observer, for any event
# history. This proves fresh-start identity/order/uniqueness, not the separate
# initial certificate, configuration validity, or native initialization boundary.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/Semantics.bend as S
import ../../Foundations.bend as F
import ../../ProtocolService.bend as Q
import ../../HostTransitions.bend as Host
import ../../SourceService.bend as Source
import ../specification/ServiceLaws.bend as E
import ../phases/PreparePhases.bend as V
import ../phases/InvalidationPhases.bend as N
import ./EventObserver.bend as O

def boot_snapshot(fact: E.Fact) -> Maybe<&2, E.Snapshot>:
  match fact:
    case E.Boot{snapshot}: Some{snapshot}
    case _: None{}

def phase_has_no_boot(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, phase: V.PreparationEvent) ->
  {boot_snapshot(V.fact(c, binding, public, phase)) == None{} : Maybe<&2, E.Snapshot>}:
  match phase:
    case V.WireReceived{wire}: {==}
    case V.IdentityEstablished{wire, context}: {==}
    case V.Accepted{wire, context}: {==}
    case V.Refuted{wire, context}: {==}
    case V.PrimitiveFailed{stage, id, fatal}: {==}
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

def core_has_no_boot(mode: Bool, -fact: I.Fact) ->
  {boot_snapshot(E.core_fact(mode, fact)) == None{} : Maybe<&2, E.Snapshot>}:
  match mode:
    case False{}: {==}
    case True{}: {==}

def event_has_no_boot(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, event: O.AuditEvent) ->
  {boot_snapshot(O.fact(c, binding, public, event)) == None{} : Maybe<&2, E.Snapshot>}:
  match event:
    case O.Core{mode, code, frame}: core_has_no_boot(mode, Q.fact_of_frame(c, Source.program(binding, Host.origin(public, code)), frame))
    case O.BoundCore{mode, origin, frame}: core_has_no_boot(mode, Q.fact_of_frame(c, Source.program(binding, origin), frame))
    case O.Preparation{phase}: phase_has_no_boot(c, binding, public, phase)
    case O.Invalidation{N.InvalidationBase{phase}}: phase_has_no_boot(c, binding, public, phase)
    case O.Invalidation{N.RegistryRemoved{handle, before, after}}: {==}
    case O.Selection{snapshot}: {==}
    case O.Resolution{raw, entry, context}: {==}
    case O.Publication{mode, response, bytes, before, after}: {==}

def boot_cannot_equal_nonboot(-snapshot: E.Snapshot, -other: E.Fact,
  none: {boot_snapshot(other) == None{} : Maybe<&2, E.Snapshot>}, same: {E.Boot{snapshot} == other : E.Fact}) -> Empty:
  F.none_negative_some(E.Snapshot, snapshot, Equal.sym(Maybe<&2, E.Snapshot>, Some{snapshot}, None{},
    Equal.trans(Maybe<&2, E.Snapshot>, Some{snapshot}, boot_snapshot(other), None{}, Equal.cong(E.Fact, Maybe<&2, E.Snapshot>, boot_snapshot, E.Boot{snapshot}, other, same), none)))

def cofact_has_no_boot(+event: O.AuditEvent, -snapshot: E.Snapshot, cofact: O.PublicationFact(event, E.Boot{snapshot})) -> Empty:
  match event:
    case O.Core{mode, code, frame}: cofact
    case O.BoundCore{mode, origin, frame}: cofact
    case O.Preparation{phase}: cofact
    case O.Invalidation{phase}: cofact
    case O.Selection{before}: cofact
    case O.Resolution{raw, entry, context}: cofact
    case O.Publication{+mode, response, bytes, before, +after}:
      boot_cannot_equal_nonboot(snapshot, E.core_fact(mode, I.Published{E.database(after)}), core_has_no_boot(mode, I.Published{E.database(after)}), cofact)

def relation_has_no_boot(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +event: O.AuditEvent, -snapshot: E.Snapshot,
  related: O.RelFact(c, binding, public, event, E.Boot{snapshot})) -> Empty:
  match related:
    case L.Left{canonical}: boot_cannot_equal_nonboot(snapshot, O.fact(c, binding, public, event), event_has_no_boot(c, binding, public, event), canonical)
    case L.Right{cofact}: cofact_has_no_boot(event, snapshot, cofact)

def BootPayload(-actual: E.Snapshot, fact: E.Fact) -> Type:
  match fact:
    case E.Boot{expected}: {actual == expected : E.Snapshot}
    case _: Unit


def boot_payload_is_injective(-actual: E.Snapshot, -expected: E.Snapshot, same: {E.Boot{actual} == E.Boot{expected} : E.Fact}) -> {actual == expected : E.Snapshot}:
  %same : BootPayload(actual, _)
  {==}

def initial_boot_is_exact(~c: S.Configuration, ~seed: Unit -> D.State, ~pi: String, -instance: String,
  -x: I.Scenario, at: Nat, -snapshot: E.Snapshot, observed: O.InitialObserved(c, seed, pi, instance, x, at, E.Boot{snapshot})) ->
  L.E<{at == 2n : Nat}, L.E<{x == I.Initialize{0n, c, seed(Unit{}), pi} : I.Scenario}, {snapshot == E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}} : E.Snapshot}>>:
  match at:
    case 0n:
      match observed:
        case L.Both{scenario, fact}:
          L.ex_false(L.E<{0n == 2n : Nat}, L.E<{x == I.Initialize{0n, c, seed(Unit{}), pi} : I.Scenario}, {snapshot == E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}} : E.Snapshot}>>,
            boot_cannot_equal_nonboot(snapshot, E.Ordinary{I.ProofInitialAccepts{}}, {==}, fact))
    case 1n+k:
      match k:
        case 0n:
          match observed:
            case L.Both{scenario, fact}:
              L.ex_false(L.E<{1n == 2n : Nat}, L.E<{x == I.Initialize{0n, c, seed(Unit{}), pi} : I.Scenario}, {snapshot == E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}} : E.Snapshot}>>,
                boot_cannot_equal_nonboot(snapshot, E.Ordinary{I.InstanceStarted{seed(Unit{})}}, {==}, fact))
        case 1n+j:
          match j:
            case 0n:
              match observed:
                case L.Both{scenario, fact}:
                  L.Both{{==}, L.Both{scenario, boot_payload_is_injective(snapshot, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, fact)}}
            case 1n+rest:
              match observed:
                case L.Both{scenario, fact}:
                  L.ex_false(L.E<{Succ{Succ{Succ{rest}}} == 2n : Nat}, L.E<{x == I.Initialize{0n, c, seed(Unit{}), pi} : I.Scenario}, {snapshot == E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}} : E.Snapshot}>>, fact)

def Exact(~c: S.Configuration, ~seed: Unit -> D.State, ~pi: String, ~instance: String, -x: I.Scenario, -at: Nat, -snapshot: E.Snapshot) -> Type:
  L.E<{at == 2n : Nat}, L.E<{x == I.Initialize{0n, c, seed(Unit{}), pi} : I.Scenario}, {snapshot == E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}} : E.Snapshot}>>

law every_boot_observation_is_the_same_initial_event_even_with_publication_cofacts_and_arbitrary_prior_calls:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~items: List<&2, O.Item>
  for ~instance: String
  for -k: String
  for -x: I.Scenario
  for +at: Nat
  for -snapshot: E.Snapshot
  for observed: E.observes(O.environment(binding, public, c, seed, pi, artifacts, items, instance), k, x, at, E.Boot{snapshot})
  Exact(c, seed, pi, instance, x, at, snapshot)
def every_boot_observation_is_the_same_initial_event_even_with_publication_cofacts_and_arbitrary_prior_calls(binding, public, c, seed, pi, artifacts, items, instance, k, x, at, snapshot, observed):
  match observed:
    case L.Both{artifact, L.Left{initial}}: initial_boot_is_exact(c, seed, pi, instance, x, at, snapshot, initial)
    case L.Both{artifact, L.Right{(+index, +item, L.Both{time, L.Both{query, L.Both{scenario, relation}}})}}:
      L.ex_false(Exact(c, seed, pi, instance, x, at, snapshot), relation_has_no_boot(c, binding, public, O.event(item), snapshot, relation))


def at_initial(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~items: List<&2, O.Item>, ~instance: String, +k: String,
  artifact: {k == Source.artifact(binding) : String}) ->
  E.Rule1(O.environment(binding, public, c, seed, pi, artifacts, items, instance),
    E.Boot{E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}}, k, I.Initialize{0n, c, seed(Unit{}), pi}, 2n):
  L.Both{{==}, L.Both{(1n, L.Both{{==}, L.Both{artifact, L.Left{L.Both{{==}, {==}}}}}),
    y => u => other => same_run => observed => every_boot_observation_is_the_same_initial_event_even_with_publication_cofacts_and_arbitrary_prior_calls(binding, public, c, seed, pi, artifacts, items, instance, k, y, u, other, observed)}}


def from_exact(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~items: List<&2, O.Item>, ~instance: String, +k: String,
  -x: I.Scenario, -at: Nat, -snapshot: E.Snapshot, artifact: {k == Source.artifact(binding) : String},
  exact: Exact(c, seed, pi, instance, x, at, snapshot)) ->
  E.Rule1(O.environment(binding, public, c, seed, pi, artifacts, items, instance), E.Boot{snapshot}, k, x, at):
  match exact:
    case L.Both{time, L.Both{scenario, state}}:
      %Equal.sym(Nat, at, 2n, time) : E.Rule1(O.environment(binding, public, c, seed, pi, artifacts, items, instance), E.Boot{snapshot}, k, x, _)
      %Equal.sym(I.Scenario, x, I.Initialize{0n, c, seed(Unit{}), pi}, scenario) : E.Rule1(O.environment(binding, public, c, seed, pi, artifacts, items, instance), E.Boot{snapshot}, k, _, 2n)
      %Equal.sym(E.Snapshot, snapshot, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, state) : E.Rule1(O.environment(binding, public, c, seed, pi, artifacts, items, instance), E.Boot{_}, k, I.Initialize{0n, c, seed(Unit{}), pi}, 2n)
      at_initial(binding, public, c, seed, pi, artifacts, items, instance, k, artifact)


law every_actual_observed_boot_follows_the_complete_unchanged_rule1_without_any_native_or_validity_premise:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~items: List<&2, O.Item>
  for ~instance: String
  for +k: String
  for -x: I.Scenario
  for +at: Nat
  for -snapshot: E.Snapshot
  for observed: E.observes(O.environment(binding, public, c, seed, pi, artifacts, items, instance), k, x, at, E.Boot{snapshot})
  E.Rule1(O.environment(binding, public, c, seed, pi, artifacts, items, instance), E.Boot{snapshot}, k, x, at)
def every_actual_observed_boot_follows_the_complete_unchanged_rule1_without_any_native_or_validity_premise(binding, public, c, seed, pi, artifacts, items, instance, k, x, at, snapshot, observed):
  match observed:
    case L.Both{+artifact, L.Left{initial}}:
      from_exact(binding, public, c, seed, pi, artifacts, items, instance, k, x, at, snapshot, artifact, initial_boot_is_exact(c, seed, pi, instance, x, at, snapshot, initial))
    case L.Both{artifact, L.Right{(+index, +item, L.Both{time, L.Both{query, L.Both{scenario, relation}}})}}:
      L.ex_false(E.Rule1(O.environment(binding, public, c, seed, pi, artifacts, items, instance), E.Boot{snapshot}, k, x, at), relation_has_no_boot(c, binding, public, O.event(item), snapshot, relation))
