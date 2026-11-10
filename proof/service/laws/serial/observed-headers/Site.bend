# Connect full RelFact+actual Item/block queries to the exact decoded header
# grammar. The originating event, reception and selected DB are not replaced.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Semantics.bend as S
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/Decode.bend as Decode
import ../../../model/serial/SerialItems.bend as Items
import ./HeaderData.bend as H
import ./HeaderFact.bend as Fact
import ./BlockLayout.bend as Block
import ./Projection.bend as Projection
import ./Recover.bend as Recover


def rebuilt_view(point: H.Point, +wire: W.WireRequest, +context: Maybe<&2, D.Context>) ->
  {H.fact(Fact.expected(point, wire, context)) == H.expected(point, wire, context) : H.View}:
  match point:
    case H.WirePoint{}: {==}
    case H.IdentityPoint{}: {==}


def rebuilt_relevant(+point: H.Point, +wire: W.WireRequest, +context: Maybe<&2, D.Context>) -> H.Relevant(H.fact(Fact.expected(point, wire, context))):
  %Equal.sym(H.View, H.fact(Fact.expected(point, wire, context)), H.expected(point, wire, context), rebuilt_view(point, wire, context)) : H.Relevant(_)
  H.expected_relevant(point, wire, context)


def actual_view(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +event: O.AuditEvent, +point: H.Point, +wire: W.WireRequest, +context: Maybe<&2, D.Context>,
  relation: O.RelFact(c, binding, public, event, Fact.expected(point, wire, context))) ->
  {H.event(event) == H.expected(point, wire, context) : H.View}:
  Equal.trans(H.View, H.event(event), H.fact(Fact.expected(point, wire, context)), H.expected(point, wire, context),
    Projection.actual_event_view(c, binding, public, event, Fact.expected(point, wire, context), rebuilt_relevant(point, wire, context), relation), rebuilt_view(point, wire, context))


def Hit(~c: S.Configuration, +block: Engine.Block, +point: H.Point, -index: Nat, -item: O.Item, +wire: W.WireRequest, +context: Maybe<&2, D.Context>) -> Type:
  &event: O.AuditEvent -> L.E<{item == O.Item{Engine.world(block), E.database(Chain.block_before(block)), Block.input(block), event} : O.Item},
    Recover.Seen(Chain.block_before(block), Block.events(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), Block.input(block))), point, index, wire, context)>


def from_stamp(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +script: List<&2, Engine.Job>, +initial_ordinal: Nat, +initial: E.Snapshot, +owner: Nat, +block: Engine.Block,
  +point: H.Point, +index: Nat, +item: O.Item, +wire: W.WireRequest, +context: Maybe<&2, D.Context>,
  block_found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, initial_ordinal, initial)), owner) == Some{block} : Maybe<&2, Engine.Block>},
  relation: O.RelFact(c, binding, public, O.event(item), Fact.expected(point, wire, context)),
  origin: Items.StampedHit(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), Block.events(block), index, item)) -> Hit(c, block, point, index, item, wire, context):
  match origin:
    case (+event, L.Both{found, +exact}):
      (event, L.Both{exact,
        Recover.every_actual_block_header_query_recovers_its_real_decoding_prefix_and_authentication(c, binding, public, script, initial_ordinal, initial, owner, block, point, index, event, wire, context, block_found, found,
          Equal.trans(H.View, H.event(event), H.event(O.event(item)), H.expected(point, wire, context),
            Equal.cong(O.AuditEvent, H.View, H.event, event, O.event(item),
              Equal.sym(O.AuditEvent, O.event(item), event, Equal.cong(O.Item, O.AuditEvent, O.event, item,
                O.Item{Engine.world(block), E.database(Chain.block_before(block)), Block.input(block), event}, exact))), actual_view(c, binding, public, O.event(item), point, wire, context, relation)))})


def from_block_event(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +script: List<&2, Engine.Job>, +initial_ordinal: Nat, +initial: E.Snapshot, +owner: Nat, +block: Engine.Block,
  +point: H.Point, +index: Nat, +item: O.Item, +wire: W.WireRequest, +context: Maybe<&2, D.Context>,
  block_found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, initial_ordinal, initial)), owner) == Some{block} : Maybe<&2, Engine.Block>},
  relation: O.RelFact(c, binding, public, O.event(item), Fact.expected(point, wire, context)),
  origin: Items.BlockEventHit(block, index, item)) -> Hit(c, block, point, index, item, wire, context):
  match block:
    case Engine.Block{+ordinal, +selected, +input, +before, +run}:
      from_stamp(c, binding, public, script, initial_ordinal, initial, owner, Engine.Block{ordinal, selected, input, before, run}, point, index, item, wire, context, block_found, relation, origin)


law every_actual_header_item_recovers_the_same_job_reception_selected_database_and_exact_header_site:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +initial_ordinal: Nat
  for +initial: E.Snapshot
  for +owner: Nat
  for +block: Engine.Block
  for +point: H.Point
  for +index: Nat
  for +item: O.Item
  for +wire: W.WireRequest
  for +context: Maybe<&2, D.Context>
  for block_found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, initial_ordinal, initial)), owner) == Some{block} : Maybe<&2, Engine.Block>}
  for item_found: {B.query(O.Item, Engine.block_items(block), index) == Some{item} : Maybe<&2, O.Item>}
  for relation: O.RelFact(c, binding, public, O.event(item), Fact.expected(point, wire, context))
  Hit(c, block, point, index, item, wire, context)
def every_actual_header_item_recovers_the_same_job_reception_selected_database_and_exact_header_site(c, binding, public, script, initial_ordinal, initial, owner, block, point, index, item, wire, context, block_found, item_found, relation):
  from_block_event(c, binding, public, script, initial_ordinal, initial, owner, block, point, index, item, wire, context, block_found, relation,
    Items.an_actual_block_item_query_recovers_its_same_exact_local_source_event_and_origin(block, index, item, item_found))
