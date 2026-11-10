# Causal false target: preserve the actual observation and change only its demanded conclusion.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/Semantics.bend as S
import ../../../proof/Foundations.bend as F
import ../../../proof/ProtocolService.bend as Q
import ../../../proof/HostTransitions.bend as Host
import ../../../proof/SourceService.bend as Source
import ../../../proof/service/specification/ServiceLaws.bend as E
import ../../../proof/service/phases/PreparePhases.bend as V
import ../../../proof/service/phases/InvalidationPhases.bend as N
import ../../../proof/service/model/EventObserver.bend as O
import ../../../proof/service/model/InitialBoot.bend as Actual

law false_negative_BootChangesResponse:
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
  E.Rule1(O.environment(binding, public, c, seed, pi, artifacts, items, instance), E.Boot{E.Snapshot{E.instance(snapshot), E.database(snapshot), [0], E.registry(snapshot)}}, k, x, at)
def false_negative_BootChangesResponse(binding, public, c, seed, pi, artifacts, items, instance, k, x, at, snapshot, observed):
  Actual.every_actual_observed_boot_follows_the_complete_unchanged_rule1_without_any_native_or_validity_premise(binding, public, c, seed, pi, artifacts, items, instance, k, x, at, snapshot, observed)
