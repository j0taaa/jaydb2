# Actual whole-history Current at the exact item time and actual block-local
# replay snapshot. No isolated-observer equivalence or erased metadata gap.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Logic.bend as L
import ../../../../contract/PreparedLaws.bend as H
import ../../../../contract/Semantics.bend as S
import ../../../Foundations.bend as F
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ./SerialItems.bend as Items
import ../EventObserver.bend as O
import ../EventHistory.bend as T
import ../FrameBounds.bend as B
import ./Chain.bend as Chain
import ./Engine.bend as Engine
import ./PrefixReplay.bend as Replay
import ./SerialCurrent.bend as Current


def actual_hit_has_exact_prefix_count(+events: List<&2, O.Item>, +index: Nat, -item: O.Item,
  found: {B.query(O.Item, events, index) == Some{item} : Maybe<&2, O.Item>}) -> {B.count(O.Item, T.take(index, events)) == index : Nat}:
  match events index:
    case Nil{} index: L.ex_false({B.count(O.Item, T.take(index, Nil{})) == index : Nat}, F.none_negative_some(O.Item, item, found))
    case Con{head, rest} 0n: {==}
    case Con{head, +rest} 1n+ +previous:
      Equal.cong(Nat, Nat, n => Succ{n}, B.count(O.Item, T.take(previous, rest)), previous,
        actual_hit_has_exact_prefix_count(rest, previous, item, found))


def move_current_time(~a: E.Environment, ~c: S.Configuration, -k: String, -item: O.Item,
  -before: Nat, -after: Nat, -snapshot: E.Snapshot, same: {before == after : Nat},
  actual: E.Current(a, k, O.scenario(c, item), before, snapshot)) -> E.Current(a, k, O.scenario(c, item), after, snapshot):
  %same : E.Current(a, k, O.scenario(c, item), _, snapshot)
  actual


law every_actual_serial_item_has_complete_current_at_its_actual_global_time:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~script: List<&2, Engine.Job>
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~instance: String
  for +global: Nat
  for +item: O.Item
  for found: {B.query(O.Item, Current.source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), global) == Some{item} : Maybe<&2, O.Item>}
  E.Current(O.environment(binding, public, c, seed, pi, artifacts, Current.source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), instance),
    Source.artifact(binding), O.scenario(c, item), O.time(global),
    Current.after_prefix(global, Current.source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}))
def every_actual_serial_item_has_complete_current_at_its_actual_global_time(c, binding, public, script, seed, pi, artifacts, instance, global, item, found):
  match item:
    case O.Item{world, selected, input, event}:
      move_current_time(O.environment(binding, public, c, seed, pi, artifacts, Current.source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), instance),
        c, Source.artifact(binding), O.Item{world, selected, input, event},
        Current.at_prefix(global, Current.source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), O.time(global),
        Current.after_prefix(global, Current.source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}),
        Equal.cong(Nat, Nat, O.time, B.count(O.Item, T.take(global, Current.source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}))), global,
          actual_hit_has_exact_prefix_count(Current.source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), global, O.Item{world, selected, input, event}, found)),
        Current.actual_serial_history_derives_complete_current_at_every_internal_prefix(c, binding, public, script, seed, pi, artifacts, instance, world, input, selected, global))


law actual_serial_current_at_an_item_uses_its_exact_local_block_replay:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~script: List<&2, Engine.Job>
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~instance: String
  for +owner: Nat
  for +block: Engine.Block
  for +global: Nat
  for +local: Nat
  for +item: O.Item
  for global_found: {B.query(O.Item, Current.source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), global) == Some{item} : Maybe<&2, O.Item>}
  for block_found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner) == Some{block} : Maybe<&2, Engine.Block>}
  for item_found: {B.query(O.Item, Engine.block_items(block), local) == Some{item} : Maybe<&2, O.Item>}
  for position: {global == Nat.add(Items.prefix_size(Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner), local) : Nat}
  E.Current(O.environment(binding, public, c, seed, pi, artifacts, Current.source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), instance),
    Source.artifact(binding), O.scenario(c, item), O.time(global), T.finish(T.take(local, Engine.block_items(block)), Chain.block_before(block)))
def actual_serial_current_at_an_item_uses_its_exact_local_block_replay(c, binding, public, script, seed, pi, artifacts, instance, owner, block, global, local, item, global_found, block_found, item_found, position):
  %Replay.actual_serial_item_prefix_replays_from_its_exact_selected_block_snapshot(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, owner, block, global, local, item, block_found, item_found, position) :
    E.Current(O.environment(binding, public, c, seed, pi, artifacts, Current.source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), instance), Source.artifact(binding), O.scenario(c, item), O.time(global), _)
  every_actual_serial_item_has_complete_current_at_its_actual_global_time(c, binding, public, script, seed, pi, artifacts, instance, global, item, global_found)
