# Exact originating event and physical call of an actual block-local Item.
import Base
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/Semantics.bend as S
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/SerialItems.bend as Items
import ../observed-headers/Audit.bend as Audit
import ../observed-headers/BlockLayout.bend as Block

def source_query(+block: Engine.Block, +index: Nat, +item: O.Item,
  found: {B.query(O.Item, Engine.block_items(block), index) == Some{item} : Maybe<&2, O.Item>}) ->
  {B.query(O.Item, Engine.stamp(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), Block.events(block)), index) == Some{item} : Maybe<&2, O.Item>}:
  %Audit.block_items(block) : {B.query(O.Item, _, index) == Some{item} : Maybe<&2, O.Item>}
  found

def origin(+block: Engine.Block, +index: Nat, +item: O.Item,
  found: {B.query(O.Item, Engine.block_items(block), index) == Some{item} : Maybe<&2, O.Item>}) ->
  Items.StampedHit(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), Block.events(block), index, item):
  Items.every_stamped_item_query_recovers_its_exact_originating_audit_event(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), Block.events(block), index, item, source_query(block, index, item, found))

def scenario_from_origin(~c: S.Configuration, +block: Engine.Block, -index: Nat, +item: O.Item,
  actual: Items.StampedHit(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), Block.events(block), index, item)) ->
  {O.scenario(c, item) == I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), Block.input(block)} : I.Scenario}:
  match actual:
    case (event, L.Both{found, literal}):
      Equal.cong(O.Item, I.Scenario, value => O.scenario(c, value), item, O.Item{Engine.world(block), E.database(Chain.block_before(block)), Block.input(block), event}, literal)

def scenario(~c: S.Configuration, +block: Engine.Block, +index: Nat, +item: O.Item,
  found: {B.query(O.Item, Engine.block_items(block), index) == Some{item} : Maybe<&2, O.Item>}) ->
  {O.scenario(c, item) == I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), Block.input(block)} : I.Scenario}:
  scenario_from_origin(c, block, index, item, origin(block, index, item, found))
