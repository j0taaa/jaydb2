# Derive the exact state BEFORE an actual block from complete earlier block
# replay and actual Engine links. No Current/final state/native trace premise.
import Base
import ../../../../contract/Logic.bend as L
import ../../../../contract/Semantics.bend as S
import ../../../Foundations.bend as F
import ../../../SourceService.bend as Source
import ../../../ProtocolService.bend as Q
import ../../specification/ServiceLaws.bend as E
import ./SerialItems.bend as Items
import ../EventObserver.bend as O
import ../EventHistory.bend as T
import ../FrameBounds.bend as B
import ../InvalidationPrefix.bend as Append
import ./BlockHistory.bend as Blocks
import ./Chain.bend as Chain
import ./Common.bend as C
import ./Engine.bend as Engine
import ./SerialHistory.bend as History


def actual_finish_from_previous(+block: Engine.Block, +previous: E.Snapshot,
  same: {Chain.block_before(block) == previous : E.Snapshot}, actual: History.BlockSound(block)) ->
  {T.finish(Engine.block_items(block), previous) == Engine.after(block) : E.Snapshot}:
  match actual:
    case L.Both{coherent, final}:
      Equal.trans(E.Snapshot, T.finish(Engine.block_items(block), previous), T.finish(Engine.block_items(block), Chain.block_before(block)), Engine.after(block),
        Equal.cong(E.Snapshot, E.Snapshot, before => T.finish(Engine.block_items(block), before), previous, Chain.block_before(block),
          Equal.sym(E.Snapshot, Chain.block_before(block), previous, same)), final)


def before_snapshot(+blocks: List<&2, Engine.Block>, +ordinal: Nat, +previous: E.Snapshot, +owner: Nat, +block: Engine.Block,
  linked: Chain.Linked(ordinal, previous, blocks), actual: Blocks.All(blocks),
  found: {B.query(Engine.Block, blocks, owner) == Some{block} : Maybe<&2, Engine.Block>}) ->
  {T.finish(Items.before_items(blocks, owner), previous) == Chain.block_before(block) : E.Snapshot}:
  match blocks owner linked actual:
    case Nil{} _ _ _:
      L.ex_false({T.finish(Items.before_items(Nil{}, owner), previous) == Chain.block_before(block) : E.Snapshot}, F.none_negative_some(Engine.Block, block, found))
    case Con{Engine.Block{+number, +selected, +input, +before, +run}, rest} 0n L.Both{number_same, L.Both{same, L.Both{guard, later_links}}} L.Both{head_history, later_history}:
      Equal.trans(E.Snapshot, previous, before, Chain.block_before(block), Equal.sym(E.Snapshot, before, previous, same),
        Equal.cong(Engine.Block, E.Snapshot, Chain.block_before, Engine.Block{number, selected, input, before, run}, block,
          F.some_injective(Engine.Block, Engine.Block{number, selected, input, before, run}, block, found)))
    case Con{Engine.Block{+number, +selected, +input, +before, +run}, +rest} 1n+k L.Both{number_same, L.Both{same, L.Both{guard, later_links}}} L.Both{head_history, later_history}:
      Equal.trans(E.Snapshot,
        T.finish(T.append(Engine.block_items(Engine.Block{number, selected, input, before, run}), Items.before_items(rest, k)), previous),
        T.finish(Items.before_items(rest, k), T.finish(Engine.block_items(Engine.Block{number, selected, input, before, run}), previous)), Chain.block_before(block),
        Append.adjoining_phase_prefixes_has_the_exact_sequential_snapshot(Engine.block_items(Engine.Block{number, selected, input, before, run}), Items.before_items(rest, k), previous),
        Equal.trans(E.Snapshot,
          T.finish(Items.before_items(rest, k), T.finish(Engine.block_items(Engine.Block{number, selected, input, before, run}), previous)),
          T.finish(Items.before_items(rest, k), C.snapshot(run)), Chain.block_before(block),
          Equal.cong(E.Snapshot, E.Snapshot, snapshot => T.finish(Items.before_items(rest, k), snapshot),
            T.finish(Engine.block_items(Engine.Block{number, selected, input, before, run}), previous), C.snapshot(run),
            actual_finish_from_previous(Engine.Block{number, selected, input, before, run}, previous, same, head_history)),
          before_snapshot(rest, Engine.next(selected, number), C.snapshot(run), k, block, later_links, later_history, found)))


law every_actual_serial_block_receives_the_exact_complete_prior_history_snapshot:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +ordinal: Nat
  for +before: E.Snapshot
  for +owner: Nat
  for +block: Engine.Block
  for found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), owner) == Some{block} : Maybe<&2, Engine.Block>}
  {T.finish(Items.before_items(Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), owner), before) == Chain.block_before(block) : E.Snapshot}
def every_actual_serial_block_receives_the_exact_complete_prior_history_snapshot(c, binding, public, script, ordinal, before, owner, block, found):
  before_snapshot(Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), ordinal, before, owner, block,
    Chain.every_actual_serial_prefix_keeps_exact_state_and_registry_and_selection_links(c, binding, public, script, ordinal, before),
    Blocks.actual_serial_engine_derives_the_exact_local_history_of_every_retained_block(c, binding, public, script, ordinal, before), found)


def slice_from_copies(+whole: Engine.PrefixRun, +ordinal: Nat, +before: E.Snapshot,
  +owner: Nat, +block: Engine.Block, +global: Nat, +local: Nat, -item: O.Item,
  flat: Items.Flat(whole), linked: Chain.Linked(ordinal, before, Engine.blocks(whole)), actual: Blocks.All(Engine.blocks(whole)),
  block_queries: L.E<{B.query(Engine.Block, Engine.blocks(whole), owner) == Some{block} : Maybe<&2, Engine.Block>},
    {B.query(Engine.Block, Engine.blocks(whole), owner) == Some{block} : Maybe<&2, Engine.Block>}>,
  item_found: {B.query(O.Item, Engine.block_items(block), local) == Some{item} : Maybe<&2, O.Item>},
  position: {global == Nat.add(Items.prefix_size(Engine.blocks(whole), owner), local) : Nat}) ->
  {T.finish(T.take(global, Engine.items(whole)), before) == T.finish(T.take(local, Engine.block_items(block)), Chain.block_before(block)) : E.Snapshot}:
  match block_queries:
    case L.Both{for_slice, for_snapshot}:
      Equal.trans(E.Snapshot, T.finish(T.take(global, Engine.items(whole)), before), T.finish(T.take(global, Items.flatten(Engine.blocks(whole))), before),
        T.finish(T.take(local, Engine.block_items(block)), Chain.block_before(block)),
        Equal.cong(List<&2, O.Item>, E.Snapshot, events => T.finish(T.take(global, events), before), Engine.items(whole), Items.flatten(Engine.blocks(whole)), flat),
        Equal.trans(E.Snapshot, T.finish(T.take(global, Items.flatten(Engine.blocks(whole))), before),
          T.finish(T.append(Items.before_items(Engine.blocks(whole), owner), T.take(local, Engine.block_items(block))), before),
          T.finish(T.take(local, Engine.block_items(block)), Chain.block_before(block)),
          Equal.cong(List<&2, O.Item>, E.Snapshot, events => T.finish(events, before),
            T.take(global, Items.flatten(Engine.blocks(whole))), T.append(Items.before_items(Engine.blocks(whole), owner), T.take(local, Engine.block_items(block))),
            Items.a_located_item_derives_its_exact_prior_block_and_local_item_prefix(Engine.blocks(whole), owner, block, global, local, item, for_slice, item_found, position)),
          Equal.trans(E.Snapshot, T.finish(T.append(Items.before_items(Engine.blocks(whole), owner), T.take(local, Engine.block_items(block))), before),
            T.finish(T.take(local, Engine.block_items(block)), T.finish(Items.before_items(Engine.blocks(whole), owner), before)),
            T.finish(T.take(local, Engine.block_items(block)), Chain.block_before(block)),
            Append.adjoining_phase_prefixes_has_the_exact_sequential_snapshot(Items.before_items(Engine.blocks(whole), owner), T.take(local, Engine.block_items(block)), before),
            Equal.cong(E.Snapshot, E.Snapshot, snapshot => T.finish(T.take(local, Engine.block_items(block)), snapshot),
              T.finish(Items.before_items(Engine.blocks(whole), owner), before), Chain.block_before(block),
              before_snapshot(Engine.blocks(whole), ordinal, before, owner, block, linked, actual, for_snapshot)))))


law actual_serial_item_prefix_replays_from_its_exact_selected_block_snapshot:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +ordinal: Nat
  for +before: E.Snapshot
  for +owner: Nat
  for +block: Engine.Block
  for +global: Nat
  for +local: Nat
  for -item: O.Item
  for block_found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), owner) == Some{block} : Maybe<&2, Engine.Block>}
  for item_found: {B.query(O.Item, Engine.block_items(block), local) == Some{item} : Maybe<&2, O.Item>}
  for position: {global == Nat.add(Items.prefix_size(Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), owner), local) : Nat}
  {T.finish(T.take(global, Engine.items(Engine.run(c, binding, public, script, ordinal, before))), before) ==
    T.finish(T.take(local, Engine.block_items(block)), Chain.block_before(block)) : E.Snapshot}
def actual_serial_item_prefix_replays_from_its_exact_selected_block_snapshot(c, binding, public, script, ordinal, before, owner, block, global, local, item, block_found, item_found, position):
  slice_from_copies(Engine.run(c, binding, public, script, ordinal, before), ordinal, before, owner, block, global, local, item,
    Items.actual_serial_items_are_exactly_the_flattened_actual_retained_blocks(c, binding, public, script, ordinal, before),
    Chain.every_actual_serial_prefix_keeps_exact_state_and_registry_and_selection_links(c, binding, public, script, ordinal, before),
    Blocks.actual_serial_engine_derives_the_exact_local_history_of_every_retained_block(c, binding, public, script, ordinal, before),
    Q.equality_reopenable(Maybe<&2, Engine.Block>, B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), owner), Some{block}, block_found),
    item_found, position)
