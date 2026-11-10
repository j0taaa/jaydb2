# Complete ReceiptPrepared Rule4 from ANY actual full-history observation.
# PreparedReceipt needs ZERO native premises; InvalidatedReceipt needs only
# the existing physical-reception family. Source/current/guards are DERIVED.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Semantics.bend as S
import ../../../../../contract/Resources.bend as X
import ../../../../SourceService.bend as Binding
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/Dispatch.bend as Dispatch
import ../header/History.bend as History
import ../../../model/serial/GeneratedBlocks.bend as Generated
import ../ObservationLocation.bend as Location
import ../observed-headers/BlockLayout.bend as Layout
import ../observed-sealing/Recovery.bend as DecodeData
import ../core-conclusions/ItemOrigin.bend as Origin
import ./Projection.bend as Projection
import ./AtSlot.bend as Slot

# Initial facts cannot be receipt preparations. This preserves the original
# observation relation rather than assuming every relevant fact is listed.
def no_fact(+receipt: W.Receipt, +bytes: List<&2, U32>, -other: E.Fact,
  absent: {Projection.fact(other) == Projection.NoReceipt{} : Projection.View}, same: {E.ReceiptPrepared{receipt, bytes} == other : E.Fact}) -> Empty:
  %Equal.sym(Projection.View, Projection.Metadata{receipt, bytes}, Projection.NoReceipt{}, Equal.trans(Projection.View, Projection.Metadata{receipt, bytes}, Projection.fact(other), Projection.NoReceipt{},
    Equal.cong(E.Fact, Projection.View, Projection.fact, E.ReceiptPrepared{receipt, bytes}, other, same), absent)) : Projection.Void(_)
  Unit{}

def initial(~c: S.Configuration, ~seed: Unit -> D.State, ~pi: String, ~instance: String, at: Nat, +receipt: W.Receipt, +bytes: List<&2, U32>,
  impossible: O.InitialFact(c, seed, pi, instance, at, E.ReceiptPrepared{receipt, bytes})) -> Empty:
  match at:
    case Zero{}: no_fact(receipt, bytes, E.Ordinary{I.ProofInitialAccepts{}}, {==}, impossible)
    case Succ{next}:
      match next:
        case Zero{}: no_fact(receipt, bytes, E.Ordinary{I.InstanceStarted{seed(Unit{})}}, {==}, impossible)
        case Succ{later}:
          match later:
            case Zero{}: no_fact(receipt, bytes, E.Boot{E.Snapshot{instance, seed(Unit{}), [], []}}, {==}, impossible)
            case Succ{rest}: impossible

def listed(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String, -x: I.Scenario, +at: Nat, +receipt: W.Receipt, +bytes: List<&2, U32>,
  observed: E.observes(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Binding.artifact(binding), x, at, E.ReceiptPrepared{receipt, bytes})) ->
  O.ListedObserved(c, binding, public, History.items(c, binding, public, script, seed, instance), x, at, E.ReceiptPrepared{receipt, bytes}):
  match observed:
    case L.Both{artifact, L.Left{L.Both{scenario, impossible}}}:
      L.ex_false(O.ListedObserved(c, binding, public, History.items(c, binding, public, script, seed, instance), x, at, E.ReceiptPrepared{receipt, bytes}), initial(c, seed, pi, instance, at, receipt, bytes, impossible))
    case L.Both{artifact, L.Right{actual}}: actual

# Exact same physical call from the original item and retained same Job.
def call(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives, +point: Nat, +item: O.Item,
  exact: {block == Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives}) : Engine.Block},
  found: {B.query(O.Item, Engine.block_items(block), point) == Some{item} : Maybe<&2, O.Item>}) ->
  {O.scenario(c, item) == I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input} : I.Scenario}:
  Equal.trans(I.Scenario, O.scenario(c, item), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), Layout.input(block)}, I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input},
    Origin.scenario(c, block, point, item, found),
    Equal.cong(X.Reception, I.Scenario, reception => I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), reception}, Layout.input(block), input, DecodeData.input_equal(c, binding, public, block, input, primitives, exact)))

def for_job(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String, -x: I.Scenario, +at: Nat, +receipt: W.Receipt, +bytes: List<&2, U32>,
  +global: Nat, +item: O.Item, +owner: Nat, +block: Engine.Block, +point: Nat, +input: X.Reception, +primitives: Dispatch.Primitives,
  time: {at == O.time(global) : Nat}, scenario: {x == O.scenario(c, item) : I.Scenario},
  +known: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +found: {B.query(O.Item, Engine.block_items(block), point) == Some{item} : Maybe<&2, O.Item>},
  position: {global == History.position(c, binding, public, script, seed, instance, owner, point) : Nat},
  +exact: {block == Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives}) : Engine.Block},
  native: Slot.Boundary(c, binding, public, script, seed, instance, receipt),
  actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View}) ->
  E.Rule4(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.ReceiptPrepared{receipt, bytes}, Binding.artifact(binding), x, at):
  %Equal.sym(Nat, at, O.time(History.position(c, binding, public, script, seed, instance, owner, point)), Equal.trans(Nat, at, O.time(global), O.time(History.position(c, binding, public, script, seed, instance, owner, point)), time,
    Equal.cong(Nat, Nat, O.time, global, History.position(c, binding, public, script, seed, instance, owner, point), position))) : E.Rule4(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.ReceiptPrepared{receipt, bytes}, Binding.artifact(binding), x, _)
  %Equal.sym(I.Scenario, x, I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, Equal.trans(I.Scenario, x, O.scenario(c, item), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, scenario,
    call(c, binding, public, block, input, primitives, point, item, exact, found))) : E.Rule4(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.ReceiptPrepared{receipt, bytes}, Binding.artifact(binding), _, O.time(History.position(c, binding, public, script, seed, instance, owner, point)))
  Slot.actual(c, binding, public, script, seed, pi, artifacts, instance, owner, block, input, primitives, point, item, receipt, bytes, known, exact, native, actual, found)

def generated(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String, -x: I.Scenario, +at: Nat, +receipt: W.Receipt, +bytes: List<&2, U32>,
  +global: Nat, +item: O.Item, +owner: Nat, +block: Engine.Block, +point: Nat,
  time: {at == O.time(global) : Nat}, scenario: {x == O.scenario(c, item) : I.Scenario},
  +known: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  found: {B.query(O.Item, Engine.block_items(block), point) == Some{item} : Maybe<&2, O.Item>},
  position: {global == History.position(c, binding, public, script, seed, instance, owner, point) : Nat},
  native: Slot.Boundary(c, binding, public, script, seed, instance, receipt),
  actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View},
  source: Generated.GeneratedAt(c, binding, public, script, owner, block)) ->
  E.Rule4(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.ReceiptPrepared{receipt, bytes}, Binding.artifact(binding), x, at):
  match source:
    case (Engine.Job{input, primitives}, L.Both{job_found, exact}):
      for_job(c, binding, public, script, seed, pi, artifacts, instance, x, at, receipt, bytes, global, item, owner, block, point, input, primitives, time, scenario, known, found, position, exact, native, actual)

def from_location(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String, -x: I.Scenario, +at: Nat, +receipt: W.Receipt, +bytes: List<&2, U32>,
  native: Slot.Boundary(c, binding, public, script, seed, instance, receipt),
  located: Location.Located(c, binding, public, script, History.boot(seed, instance), x, at, E.ReceiptPrepared{receipt, bytes})) ->
  E.Rule4(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.ReceiptPrepared{receipt, bytes}, Binding.artifact(binding), x, at):
  match located:
    case (+global, +item, L.Both{time, L.Both{global_found, L.Both{scenario, L.Both{related, origin}}}}):
      match origin:
        case (+owner, +block, +point, L.Both{+known, L.Both{found, position}}):
          generated(c, binding, public, script, seed, pi, artifacts, instance, x, at, receipt, bytes, global, item, owner, block, point, time, scenario, known, found, position, native,
            Projection.actual_event_view(c, binding, public, O.event(item), receipt, bytes, related),
            Generated.every_actual_block_query_recovers_its_same_actual_script_job_and_computed_dispatch(c, binding, public, script, 0n, History.boot(seed, instance), owner, block, known))

law every_actual_observed_metadata_prepared_receipt_obeys_complete_authorization_rule4_before_any_later_completion:
  for ~c: S.Configuration
  for ~binding: Binding.Source
  for ~public: List<&2, Binding.FileSource>
  for ~script: List<&2, Engine.Job>
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~instance: String
  for -x: I.Scenario
  for +at: Nat
  for +receipt: W.Receipt
  for +bytes: List<&2, U32>
  for native: Slot.Boundary(c, binding, public, script, seed, instance, receipt)
  for observed: E.observes(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Binding.artifact(binding), x, at, E.ReceiptPrepared{receipt, bytes})
  E.Rule4(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.ReceiptPrepared{receipt, bytes}, Binding.artifact(binding), x, at)
def every_actual_observed_metadata_prepared_receipt_obeys_complete_authorization_rule4_before_any_later_completion(c, binding, public, script, seed, pi, artifacts, instance, x, at, receipt, bytes, native, observed):
  from_location(c, binding, public, script, seed, pi, artifacts, instance, x, at, receipt, bytes, native,
    Location.locate_listed(c, binding, public, script, History.boot(seed, instance), x, at, E.ReceiptPrepared{receipt, bytes}, listed(c, binding, public, script, seed, pi, artifacts, instance, x, at, receipt, bytes, observed)))

law every_actual_observed_preparation_receipt_frame_is_authorized_without_any_native_premise:
  for ~c: S.Configuration
  for ~binding: Binding.Source
  for ~public: List<&2, Binding.FileSource>
  for ~script: List<&2, Engine.Job>
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~instance: String
  for -x: I.Scenario
  for +at: Nat
  for +handle: String
  for +bytes: List<&2, U32>
  for observed: E.observes(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Binding.artifact(binding), x, at, E.ReceiptPrepared{W.PreparedReceipt{handle}, bytes})
  E.Rule4(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.ReceiptPrepared{W.PreparedReceipt{handle}, bytes}, Binding.artifact(binding), x, at)
def every_actual_observed_preparation_receipt_frame_is_authorized_without_any_native_premise(c, binding, public, script, seed, pi, artifacts, instance, x, at, handle, bytes, observed):
  every_actual_observed_metadata_prepared_receipt_obeys_complete_authorization_rule4_before_any_later_completion(c, binding, public, script, seed, pi, artifacts, instance, x, at, W.PreparedReceipt{handle}, bytes, Unit{}, observed)
