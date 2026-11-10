# Query-level call identity from actual successive Engine selection ordinals.
# No no-duplicates, random-string uniqueness or chosen world premise is used.
import Base
import ../../../../contract/Logic.bend as L
import ../../../../contract/Semantics.bend as S
import ../../../Foundations.bend as F
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../FrameBounds.bend as B
import ../TimeEmbedding.bend as T
import ./Engine.bend as Engine
import ./Chain.bend as Chain
import ./CallIds.bend as Names


def add_zero_right(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n: {==}
    case 1n+ +previous: Equal.cong(Nat, Nat, n => Succ{n}, Nat.add(previous, 0n), previous, add_zero_right(previous))


def add_successor_right(n: Nat, +index: Nat) -> {Nat.add(n, Succ{index}) == Succ{Nat.add(n, index)} : Nat}:
  match n:
    case 0n: {==}
    case 1n+ +previous:
      Equal.cong(Nat, Nat, n => Succ{n}, Nat.add(previous, Succ{index}), Succ{Nat.add(previous, index)}, add_successor_right(previous, index))

law a_queried_named_block_has_the_exact_initial_ordinal_plus_its_actual_index:
  for +blocks: List<&2, Engine.Block>
  for +initial: Nat
  for index: Nat
  for +block: Engine.Block
  for names: Names.Names(initial, blocks)
  for found: {B.query(Engine.Block, blocks, index) == Some{block} : Maybe<&2, Engine.Block>}
  {Chain.block_ordinal(block) == Nat.add(initial, index) : Nat}
def a_queried_named_block_has_the_exact_initial_ordinal_plus_its_actual_index(blocks, initial, index, block, names, found):
  match blocks index names:
    case Nil{} index unit:
      L.ex_false({Chain.block_ordinal(block) == Nat.add(initial, index) : Nat}, F.none_negative_some(Engine.Block, block, found))
    case Con{Engine.Block{+actual, selected, input, before, run}, rest} 0n L.Both{ordinal, later}:
      Equal.trans(Nat, Chain.block_ordinal(block), actual, Nat.add(initial, 0n),
        Equal.cong(Engine.Block, Nat, Chain.block_ordinal, block, Engine.Block{actual, selected, input, before, run},
          Equal.sym(Engine.Block, Engine.Block{actual, selected, input, before, run}, block,
            F.some_injective(Engine.Block, Engine.Block{actual, selected, input, before, run}, block, found))),
        Equal.trans(Nat, actual, initial, Nat.add(initial, 0n), ordinal, Equal.sym(Nat, Nat.add(initial, 0n), initial, add_zero_right(initial))))
    case Con{head, +rest} 1n+ +previous L.Both{ordinal, later}:
      Equal.trans(Nat, Chain.block_ordinal(block), Nat.add(Succ{initial}, previous), Nat.add(initial, Succ{previous}),
        a_queried_named_block_has_the_exact_initial_ordinal_plus_its_actual_index(rest, Succ{initial}, previous, block, later, found),
        Equal.sym(Nat, Nat.add(initial, Succ{previous}), Succ{Nat.add(initial, previous)}, add_successor_right(initial, previous)))


def previous_world(block: Engine.Block) -> {T.previous(Engine.world(block)) == Chain.block_ordinal(block) : Nat}:
  match block:
    case Engine.Block{ordinal, selected, input, before, run}: {==}


def same_world_means_same_ordinal(+first: Engine.Block, +second: Engine.Block,
  same: {Engine.world(first) == Engine.world(second) : Nat}) -> {Chain.block_ordinal(first) == Chain.block_ordinal(second) : Nat}:
  Equal.trans(Nat, Chain.block_ordinal(first), T.previous(Engine.world(first)), Chain.block_ordinal(second),
    Equal.sym(Nat, T.previous(Engine.world(first)), Chain.block_ordinal(first), previous_world(first)),
    Equal.trans(Nat, T.previous(Engine.world(first)), T.previous(Engine.world(second)), Chain.block_ordinal(second),
      Equal.cong(Nat, Nat, T.previous, Engine.world(first), Engine.world(second), same), previous_world(second)))


def equal_named_worlds_force_equal_indices(+initial: Nat, +first_index: Nat, +second_index: Nat,
  +first: Engine.Block, +second: Engine.Block,
  first_name: {Chain.block_ordinal(first) == Nat.add(initial, first_index) : Nat},
  second_name: {Chain.block_ordinal(second) == Nat.add(initial, second_index) : Nat},
  same: {Engine.world(first) == Engine.world(second) : Nat}) -> {first_index == second_index : Nat}:
  T.cancel_prefix(initial, first_index, second_index,
    Equal.trans(Nat, Nat.add(initial, first_index), Chain.block_ordinal(first), Nat.add(initial, second_index),
      Equal.sym(Nat, Chain.block_ordinal(first), Nat.add(initial, first_index), first_name),
      Equal.trans(Nat, Chain.block_ordinal(first), Chain.block_ordinal(second), Nat.add(initial, second_index),
        same_world_means_same_ordinal(first, second, same), second_name)))


def same_query_index_preserves_the_entire_block(+blocks: List<&2, Engine.Block>, +first_index: Nat, +second_index: Nat,
  +first: Engine.Block, +second: Engine.Block, +indices: {first_index == second_index : Nat},
  first_at: {B.query(Engine.Block, blocks, first_index) == Some{first} : Maybe<&2, Engine.Block>},
  second_at: {B.query(Engine.Block, blocks, second_index) == Some{second} : Maybe<&2, Engine.Block>}) ->
  L.E<{first_index == second_index : Nat}, {first == second : Engine.Block}>:
  L.Both{indices, F.some_injective(Engine.Block, first, second,
    Equal.trans(Maybe<&2, Engine.Block>, Some{first}, B.query(Engine.Block, blocks, first_index), Some{second},
      Equal.sym(Maybe<&2, Engine.Block>, B.query(Engine.Block, blocks, first_index), Some{first}, first_at),
      Equal.trans(Maybe<&2, Engine.Block>, B.query(Engine.Block, blocks, first_index), B.query(Engine.Block, blocks, second_index), Some{second},
        Equal.cong(Nat, Maybe<&2, Engine.Block>, i => B.query(Engine.Block, blocks, i), first_index, second_index, indices), second_at)))}

law one_actual_call_world_identifies_one_retained_block_index_and_complete_block_payload:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +initial: Nat
  for +before: E.Snapshot
  for +first_index: Nat
  for +second_index: Nat
  for +first: Engine.Block
  for +second: Engine.Block
  for +first_at: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, initial, before)), first_index) == Some{first} : Maybe<&2, Engine.Block>}
  for +second_at: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, initial, before)), second_index) == Some{second} : Maybe<&2, Engine.Block>}
  for same: {Engine.world(first) == Engine.world(second) : Nat}
  L.E<{first_index == second_index : Nat}, {first == second : Engine.Block}>
def one_actual_call_world_identifies_one_retained_block_index_and_complete_block_payload(c, binding, public, script, initial, before, first_index, second_index, first, second, first_at, second_at, same):
  same_query_index_preserves_the_entire_block(Engine.blocks(Engine.run(c, binding, public, script, initial, before)), first_index, second_index, first, second,
    equal_named_worlds_force_equal_indices(initial, first_index, second_index, first, second,
      a_queried_named_block_has_the_exact_initial_ordinal_plus_its_actual_index(Engine.blocks(Engine.run(c, binding, public, script, initial, before)), initial, first_index, first,
        Names.actual_serial_calls_derive_successive_unbounded_names_without_a_uniqueness_premise(c, binding, public, script, initial, before), first_at),
      a_queried_named_block_has_the_exact_initial_ordinal_plus_its_actual_index(Engine.blocks(Engine.run(c, binding, public, script, initial, before)), initial, second_index, second,
        Names.actual_serial_calls_derive_successive_unbounded_names_without_a_uniqueness_premise(c, binding, public, script, initial, before), second_at), same), first_at, second_at)
