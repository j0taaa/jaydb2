# Local provenance from an actual computed block and original item query.
# The final observed law derives HeadSource from the real retained block.
import Base
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Semantics.bend as S
import ../../../../../contract/Resources.bend as X
import ../../../../SourceService.bend as Binding
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Common.bend as C
import ../../../model/serial/Decode.bend as Decode
import ../../../model/serial/Dispatch.bend as Dispatch
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/SerialItems.bend as Items
import ../../../model/serial/GeneratedBlocks.bend as Generated
import ../observed-headers/BlockLayout.bend as Layout
import ../core-conclusions/ItemOrigin.bend as Origin
import ./Source.bend as Source
import ./Projection.bend as Projection

def Shape(~c: S.Configuration, +block: Engine.Block, -primitives: Dispatch.Primitives) -> Type:
  Source.All(c, Chain.block_before(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), Layout.input(block))), primitives, Layout.events(block))

def selected(-c: S.Configuration, +before: E.Snapshot, -decision: Decode.Decision, -primitives: Dispatch.Primitives,
  selection: Bool, +events: List<&2, O.AuditEvent>, all: Source.All(c, before, decision, primitives, events)) ->
  Source.All(c, before, decision, primitives, Engine.selected_events(selection, before, events)):
  match selection:
    case False{}: all
    case True{}: L.Both{Unit{}, all}

def computed(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, +ordinal: Nat, +before: E.Snapshot, +input: X.Reception, +primitives: Dispatch.Primitives) ->
  Shape(c, Engine.block(c, binding, public, ordinal, before, Engine.Job{input, primitives}), primitives):
  selected(c, before, Decode.decision(Decode.run(c, E.database(before), input)), primitives, Engine.selection(X.decide_reception(c, input)), C.events(Dispatch.run(c, binding, public, before, input, primitives)),
    Source.every_actual_dispatch_prepared_receipt_retains_its_original_reached_control_inputs_before_any_later_completion(c, binding, public, before, input, primitives))

def source(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives,
  exact: Generated.HeadSource(c, binding, public, block, Engine.Job{input, primitives})) -> Shape(c, block, primitives):
  %Equal.sym(Engine.Block, block, Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives}), exact) : Shape(c, _, primitives)
  computed(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), input, primitives)

def from_event(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, +block: Engine.Block, +primitives: Dispatch.Primitives, +index: Nat, +event: O.AuditEvent, +receipt: W.Receipt, +bytes: List<&2, U32>,
  all: Shape(c, block, primitives), found: {B.query(O.AuditEvent, Layout.events(block), index) == Some{event} : Maybe<&2, O.AuditEvent>},
  actual: {Projection.event(event) == Projection.Metadata{receipt, bytes} : Projection.View}) ->
  Source.Cause<c, Chain.block_before(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), Layout.input(block))), primitives, receipt, bytes>:
  %actual : Source.ViewClaim(c, Chain.block_before(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), Layout.input(block))), primitives, _)
  Source.query(c, Chain.block_before(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), Layout.input(block))), primitives, Layout.events(block), index, event, all, found)

def from_origin(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, +block: Engine.Block, +primitives: Dispatch.Primitives, +index: Nat, +item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  all: Shape(c, block, primitives), origin: Items.StampedHit(Engine.world(block), Layout.input(block), E.database(Chain.block_before(block)), Layout.events(block), index, item),
  actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View}) ->
  Source.Cause<c, Chain.block_before(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), Layout.input(block))), primitives, receipt, bytes>:
  match origin:
    case (+event, L.Both{found, exact}):
      from_event(c, binding, public, block, primitives, index, event, receipt, bytes, all, found,
        Equal.trans(Projection.View, Projection.event(event), Projection.event(O.event(item)), Projection.Metadata{receipt, bytes},
          Equal.sym(Projection.View, Projection.event(O.event(item)), Projection.event(event), Equal.cong(O.Item, Projection.View, i => Projection.event(O.event(i)), item, O.Item{Engine.world(block), E.database(Chain.block_before(block)), Layout.input(block), event}, exact)), actual))

def query(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives, +index: Nat, +item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  exact: Generated.HeadSource(c, binding, public, block, Engine.Job{input, primitives}),
  found: {B.query(O.Item, Engine.block_items(block), index) == Some{item} : Maybe<&2, O.Item>},
  actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View}) ->
  Source.Cause<c, Chain.block_before(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), Layout.input(block))), primitives, receipt, bytes>:
  from_origin(c, binding, public, block, primitives, index, item, receipt, bytes, source(c, binding, public, block, input, primitives, exact), Origin.origin(block, index, item, found), actual)
