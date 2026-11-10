# Shared prepared transaction/metadata conclusion uniqueness over complete
# mixed histories, derived from the actual owning block's local source tag.
# Both ConclusionAt alternatives are handled, not a receipt-only shortcut.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Logic.bend as L
import ../../../../contract/PreparedLaws.bend as H
import ../../../../contract/Semantics.bend as S
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../../model/EventObserver.bend as O
import ../../model/ObservationUniqueness.bend as U
import ../../model/serial/Engine.bend as Engine
import ../../model/FrameBounds.bend as B
import ../../model/serial/SerialItems.bend as Items



import ./CriticalProjection.bend as Projection
import ./CriticalUniqueness.bend as Unique
import ../../model/PreparationConclusionUniqueness.bend as Payload


def finish(-at: Nat, -expected_at: Nat, -outcome: E.Outcome, -state: D.State, -closing: Bool,
  -other: E.Outcome, -other_state: D.State, -other_closing: Bool,
  result: L.E<{at == expected_at : Nat}, {U.ConclusionView{other, other_state, other_closing} == U.ConclusionView{outcome, state, closing} : U.View}>) ->
  L.E<{at == expected_at : Nat}, L.E<{other == outcome : E.Outcome}, L.E<{other_state == state : D.State}, {other_closing == closing : Bool}>>>:
  match result:
    case L.Both{time, same}: L.Both{time, Payload.conclusion_payload(outcome, state, closing, other, other_state, other_closing, same)}


def move_state(-at: Nat, -expected_at: Nat, -outcome: E.Outcome, -state: D.State, -closing: Bool,
  -other: E.Outcome, -database: D.State, -other_state: D.State, -other_closing: Bool,
  same: {database == other_state : D.State},
  result: L.E<{at == expected_at : Nat}, L.E<{other == outcome : E.Outcome}, L.E<{database == state : D.State}, {other_closing == closing : Bool}>>>) ->
  L.E<{at == expected_at : Nat}, L.E<{other == outcome : E.Outcome}, L.E<{other_state == state : D.State}, {other_closing == closing : Bool}>>>:
  %same : L.E<{at == expected_at : Nat}, L.E<{other == outcome : E.Outcome}, L.E<{_ == state : D.State}, {other_closing == closing : Bool}>>>
  result


def returned(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~script: List<&2, Engine.Job>, ~instance: String,
  -x: I.Scenario, +owner: Nat, +block: Engine.Block, +point: Nat,
  +outcome: E.Outcome, +state: D.State, +closing: Bool, +at: Nat, other: E.Outcome, +other_state: D.State, +other_closing: Bool,
  known_at: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner) == Some{block} : Maybe<&2, Engine.Block>},
  known_world: {E.scenario_world(x) == Engine.world(block) : Nat},
  local: U.OnlyTag(3n, U.values(c, binding, public, Engine.block_items(block)), point, U.ConclusionView{outcome, state, closing}),
  concluded: E.ConclusionAt(O.environment(binding, public, c, seed, pi, artifacts, Engine.items(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), instance), Source.artifact(binding), x, at, other, other_state, other_closing)) ->
  L.E<{at == O.time(Nat.add(Items.prefix_size(Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner), point)) : Nat}, L.E<{other == outcome : E.Outcome}, L.E<{other_state == state : D.State}, {other_closing == closing : Bool}>>>:
  match other:
    case E.Transaction{+response}:
      finish(at, O.time(Nat.add(Items.prefix_size(Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner), point)), outcome, state, closing, E.Transaction{response}, other_state, other_closing,
        Unique.observed(binding, public, c, seed, pi, artifacts, script, instance, x, at,
          E.PreparedKernel{I.Concluded{response, other_state, other_closing}}, owner, block, Projection.ConclusionKind{}, point, U.ConclusionView{outcome, state, closing},
          known_at, known_world, local, Unit{}, {==}, concluded))
    case E.Receipt{+receipt}:
      match concluded:
        case (result, (+snapshot, L.Both{observed, same_state})):
          move_state(at, O.time(Nat.add(Items.prefix_size(Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner), point)), outcome, state, closing, E.Receipt{receipt}, E.database(snapshot), other_state, other_closing, same_state,
            finish(at, O.time(Nat.add(Items.prefix_size(Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner), point)), outcome, state, closing, E.Receipt{receipt}, E.database(snapshot), other_closing,
              Unique.observed(binding, public, c, seed, pi, artifacts, script, instance, x, at,
                E.ReceiptConcluded{receipt, result, snapshot, other_closing}, owner, block, Projection.ConclusionKind{}, point, U.ConclusionView{outcome, state, closing},
                known_at, known_world, local, Unit{}, {==}, observed)))


def from_actual_local_source(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~script: List<&2, Engine.Job>, ~instance: String,
  -x: I.Scenario, +owner: Nat, +block: Engine.Block, +point: Nat,
  +outcome: E.Outcome, +state: D.State, +closing: Bool,
  known_at: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner) == Some{block} : Maybe<&2, Engine.Block>},
  known_world: {E.scenario_world(x) == Engine.world(block) : Nat},
  local: U.OnlyTag(3n, U.values(c, binding, public, Engine.block_items(block)), point, U.ConclusionView{outcome, state, closing})) ->
  E.ConclusionUnique(O.environment(binding, public, c, seed, pi, artifacts, Engine.items(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), instance), Source.artifact(binding), x, O.time(Nat.add(Items.prefix_size(Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner), point)), outcome, state, closing):
  at => other => other_state => other_closing => concluded =>
    returned(binding, public, c, seed, pi, artifacts, script, instance, x, owner, block, point, outcome, state, closing, at, other, other_state, other_closing, known_at, known_world, local, concluded)
