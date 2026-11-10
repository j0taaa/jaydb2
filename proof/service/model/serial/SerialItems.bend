# Exact decomposition of ACTUAL retained Engine histories. Items are computed
# by decode/dispatch/Core; no arbitrary complete Item/outcome table is assumed.
import Base
import ../../../../contract/Logic.bend as L
import ../../../../contract/Data.bend as D
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../Foundations.bend as F
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../EventObserver.bend as O
import ../EventHistory.bend as H
import ../FrameBounds.bend as B
import ../TimeEmbedding.bend as T
import ./Common.bend as C
import ./Engine.bend as Engine
import ../ItemWorlds.bend as Clock


def flatten(blocks: List<&2, Engine.Block>) -> List<&2, O.Item>:
  match blocks:
    case Nil{}: Nil{}
    case Con{block, rest}: H.append(Engine.block_items(block), flatten(rest))


def prefix_size(blocks: List<&2, Engine.Block>, index: Nat) -> Nat:
  match blocks index:
    case Nil{} index: 0n
    case Con{head, rest} 0n: 0n
    case Con{head, rest} 1n+ +previous: Nat.add(B.count(O.Item, Engine.block_items(head)), prefix_size(rest, previous))


def Flat(+run: Engine.PrefixRun) -> Type:
  {Engine.items(run) == flatten(Engine.blocks(run)) : List<&2, O.Item>}


def append_empty(items: List<&2, O.Item>) -> {H.append(items, Nil{}) == items : List<&2, O.Item>}:
  match items:
    case Nil{}: {==}
    case Con{+head, +rest}:
      Equal.cong(List<&2, O.Item>, List<&2, O.Item>, xs => Con{head, xs}, H.append(rest, Nil{}), rest, append_empty(rest))


def stopped_flat(block: Engine.Block) -> Flat(Engine.stopped_block(block)):
  Engine.Block{ordinal, selected, input, before, run} = block
  Equal.sym(List<&2, O.Item>, H.append(Engine.block_items(Engine.Block{ordinal, selected, input, before, run}), Nil{}),
    Engine.block_items(Engine.Block{ordinal, selected, input, before, run}), append_empty(Engine.block_items(Engine.Block{ordinal, selected, input, before, run})))


def appended_flat(+block: Engine.Block, suffix: Engine.PrefixRun, following: Flat(suffix)) -> Flat(Engine.append_block(block, suffix)):
  match suffix:
    case Engine.PrefixRun{+blocks, +items, snapshot, next, waiting, closed}:
      Equal.cong(List<&2, O.Item>, List<&2, O.Item>, later => H.append(Engine.block_items(block), later),
        items, flatten(blocks), following)


def branch_flat(proceed: Bool, +block: Engine.Block, recur: Nat -> E.Snapshot -> Engine.PrefixRun,
  following: @ordinal: Nat -> @before: E.Snapshot -> Flat(recur(ordinal, before))) ->
  Flat(Engine.branch(proceed, block, recur)):
  match proceed:
    case False{}: stopped_flat(block)
    case True{}: appended_flat(block, recur(Engine.next_after(block), Engine.after(block)), following(Engine.next_after(block), Engine.after(block)))


def executed_flat(+block: Engine.Block, recur: Nat -> E.Snapshot -> Engine.PrefixRun,
  following: @ordinal: Nat -> @before: E.Snapshot -> Flat(recur(ordinal, before))) ->
  Flat(Engine.execute_block(block, recur)):
  Engine.Block{+ordinal, +selected, +input, +before, +run} = block
  branch_flat(C.continues(run), Engine.Block{ordinal, selected, input, before, run}, recur, following)

law actual_serial_items_are_exactly_the_flattened_actual_retained_blocks:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +ordinal: Nat
  for +before: E.Snapshot
  Flat(Engine.run(c, binding, public, script, ordinal, before))
def actual_serial_items_are_exactly_the_flattened_actual_retained_blocks(c, binding, public, script, ordinal, before):
  match script:
    case Nil{}: {==}
    case Con{job, +rest}:
      executed_flat(Engine.block(c, binding, public, ordinal, before, job),
        n => s => Engine.run(c, binding, public, rest, n, s),
        n => s => actual_serial_items_are_exactly_the_flattened_actual_retained_blocks(c, binding, public, rest, n, s))


def Part(-prefix: List<&2, O.Item>, -suffix: List<&2, O.Item>, -global: Nat, -item: O.Item) -> Type:
  L.Disjunction<&index: Nat -> L.E<{global == index : Nat}, {B.query(O.Item, prefix, index) == Some{item} : Maybe<&2, O.Item>}>,
    &index: Nat -> L.E<{global == Nat.add(B.count(O.Item, prefix), index) : Nat}, {B.query(O.Item, suffix, index) == Some{item} : Maybe<&2, O.Item>}>>


def raise_part(-head: O.Item, -prefix: List<&2, O.Item>, -suffix: List<&2, O.Item>, -global: Nat, -item: O.Item,
  part: Part(prefix, suffix, global, item)) -> Part(Con{head, prefix}, suffix, Succ{global}, item):
  match part:
    case L.Left{(+index, L.Both{position, found})}:
      L.Left{(Succ{index}, L.Both{Equal.cong(Nat, Nat, n => Succ{n}, global, index, position), found})}
    case L.Right{(index, L.Both{position, found})}:
      L.Right{(index, L.Both{Equal.cong(Nat, Nat, n => Succ{n}, global, Nat.add(B.count(O.Item, prefix), index), position), found})}

law an_actual_appended_item_query_derives_its_exact_phase_location:
  for +prefix: List<&2, O.Item>
  for -suffix: List<&2, O.Item>
  for global: Nat
  for -item: O.Item
  for found: {B.query(O.Item, H.append(prefix, suffix), global) == Some{item} : Maybe<&2, O.Item>}
  Part(prefix, suffix, global, item)
def an_actual_appended_item_query_derives_its_exact_phase_location(prefix, suffix, global, item, found):
  match prefix global:
    case Nil{} +global: L.Right{(global, L.Both{{==}, found})}
    case Con{head, rest} 0n: L.Left{(0n, L.Both{{==}, found})}
    case Con{head, +rest} 1n+ +previous:
      raise_part(head, rest, suffix, previous, item,
        an_actual_appended_item_query_derives_its_exact_phase_location(rest, suffix, previous, item, found))


def Located(-blocks: List<&2, Engine.Block>, -global: Nat, -item: O.Item) -> Type:
  &owner: Nat -> &block: Engine.Block -> &local: Nat ->
    L.E<{B.query(Engine.Block, blocks, owner) == Some{block} : Maybe<&2, Engine.Block>},
      L.E<{B.query(O.Item, Engine.block_items(block), local) == Some{item} : Maybe<&2, O.Item>},
        {global == Nat.add(prefix_size(blocks, owner), local) : Nat}>>


def lift_location(+head: Engine.Block, +rest: List<&2, Engine.Block>, -global: Nat, +suffix_index: Nat, -item: O.Item,
  position: {global == Nat.add(B.count(O.Item, Engine.block_items(head)), suffix_index) : Nat},
  following: Located(rest, suffix_index, item)) -> Located(Con{head, rest}, global, item):
  match following:
    case (+owner, block, +local, L.Both{block_found, L.Both{item_found, later_position}}):
      (Succ{owner}, block, local, L.Both{block_found, L.Both{item_found,
        Equal.trans(Nat, global, Nat.add(B.count(O.Item, Engine.block_items(head)), suffix_index),
          Nat.add(Nat.add(B.count(O.Item, Engine.block_items(head)), prefix_size(rest, owner)), local), position,
          Equal.trans(Nat, Nat.add(B.count(O.Item, Engine.block_items(head)), suffix_index),
            Nat.add(B.count(O.Item, Engine.block_items(head)), Nat.add(prefix_size(rest, owner), local)),
            Nat.add(Nat.add(B.count(O.Item, Engine.block_items(head)), prefix_size(rest, owner)), local),
            Equal.cong(Nat, Nat, n => Nat.add(B.count(O.Item, Engine.block_items(head)), n),
              suffix_index, Nat.add(prefix_size(rest, owner), local), later_position),
            Equal.sym(Nat, Nat.add(Nat.add(B.count(O.Item, Engine.block_items(head)), prefix_size(rest, owner)), local),
              Nat.add(B.count(O.Item, Engine.block_items(head)), Nat.add(prefix_size(rest, owner), local)),
              T.addition_associative(B.count(O.Item, Engine.block_items(head)), prefix_size(rest, owner), local))))}})


def locate_part(+head: Engine.Block, +rest: List<&2, Engine.Block>, -global: Nat, -item: O.Item,
  part: Part(Engine.block_items(head), flatten(rest), global, item),
  recurse: @index: Nat -> {B.query(O.Item, flatten(rest), index) == Some{item} : Maybe<&2, O.Item>} -> Located(rest, index, item)) ->
  Located(Con{head, rest}, global, item):
  match part:
    case L.Left{(local, L.Both{position, found})}: (0n, head, local, L.Both{{==}, L.Both{found, position}})
    case L.Right{(+index, L.Both{position, found})}: lift_location(head, rest, global, index, item, position, recurse(index, found))

law every_flattened_item_query_derives_its_exact_retained_block_and_local_item:
  for +blocks: List<&2, Engine.Block>
  for +global: Nat
  for -item: O.Item
  for found: {B.query(O.Item, flatten(blocks), global) == Some{item} : Maybe<&2, O.Item>}
  Located(blocks, global, item)
def every_flattened_item_query_derives_its_exact_retained_block_and_local_item(blocks, global, item, found):
  match blocks:
    case Nil{}: L.ex_false(Located(Nil{}, global, item), F.none_negative_some(O.Item, item, found))
    case Con{+head, +rest}:
      locate_part(head, rest, global, item, an_actual_appended_item_query_derives_its_exact_phase_location(Engine.block_items(head), flatten(rest), global, item, found),
        index => query => every_flattened_item_query_derives_its_exact_retained_block_and_local_item(rest, index, item, query))

law every_actual_engine_item_query_derives_its_exact_retained_block_and_local_item:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +ordinal: Nat
  for +before: E.Snapshot
  for +global: Nat
  for -item: O.Item
  for found: {B.query(O.Item, Engine.items(Engine.run(c, binding, public, script, ordinal, before)), global) == Some{item} : Maybe<&2, O.Item>}
  Located(Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), global, item)
def every_actual_engine_item_query_derives_its_exact_retained_block_and_local_item(c, binding, public, script, ordinal, before, global, item, found):
  every_flattened_item_query_derives_its_exact_retained_block_and_local_item(Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), global, item,
    Equal.trans(Maybe<&2, O.Item>, B.query(O.Item, flatten(Engine.blocks(Engine.run(c, binding, public, script, ordinal, before))), global),
      B.query(O.Item, Engine.items(Engine.run(c, binding, public, script, ordinal, before)), global), Some{item},
      Equal.cong(List<&2, O.Item>, Maybe<&2, O.Item>, xs => B.query(O.Item, xs, global),
        flatten(Engine.blocks(Engine.run(c, binding, public, script, ordinal, before))), Engine.items(Engine.run(c, binding, public, script, ordinal, before)),
        Equal.sym(List<&2, O.Item>, Engine.items(Engine.run(c, binding, public, script, ordinal, before)),
          flatten(Engine.blocks(Engine.run(c, binding, public, script, ordinal, before))),
          actual_serial_items_are_exactly_the_flattened_actual_retained_blocks(c, binding, public, script, ordinal, before))), found))

# Exact variable-length slices around a queried retained block. Zero-length
# blocks are retained; their prefix contribution is genuinely zero.
def before_items(blocks: List<&2, Engine.Block>, owner: Nat) -> List<&2, O.Item>:
  match blocks owner:
    case Nil{} owner: Nil{}
    case Con{head, rest} 0n: Nil{}
    case Con{head, rest} 1n+ +previous: H.append(Engine.block_items(head), before_items(rest, previous))


def after_items(blocks: List<&2, Engine.Block>, owner: Nat) -> List<&2, O.Item>:
  match blocks owner:
    case Nil{} owner: Nil{}
    case Con{head, rest} 0n: flatten(rest)
    case Con{head, rest} 1n+ +previous: after_items(rest, previous)


def append_associative(first: List<&2, O.Item>, +middle: List<&2, O.Item>, +last: List<&2, O.Item>) ->
  {H.append(H.append(first, middle), last) == H.append(first, H.append(middle, last)) : List<&2, O.Item>}:
  match first:
    case Nil{}: {==}
    case Con{+head, +rest}:
      Equal.cong(List<&2, O.Item>, List<&2, O.Item>, xs => Con{head, xs}, H.append(H.append(rest, middle), last), H.append(rest, H.append(middle, last)),
        append_associative(rest, middle, last))


def count_append(first: List<&2, O.Item>, +last: List<&2, O.Item>) ->
  {B.count(O.Item, H.append(first, last)) == Nat.add(B.count(O.Item, first), B.count(O.Item, last)) : Nat}:
  match first:
    case Nil{}: {==}
    case Con{head, +rest}:
      Equal.cong(Nat, Nat, n => Succ{n}, B.count(O.Item, H.append(rest, last)), Nat.add(B.count(O.Item, rest), B.count(O.Item, last)), count_append(rest, last))

law actual_before_items_have_the_exact_computed_prefix_size:
  for blocks: List<&2, Engine.Block>
  for owner: Nat
  {B.count(O.Item, before_items(blocks, owner)) == prefix_size(blocks, owner) : Nat}
def actual_before_items_have_the_exact_computed_prefix_size(blocks, owner):
  match blocks owner:
    case Nil{} owner: {==}
    case Con{head, rest} 0n: {==}
    case Con{+head, +rest} 1n+ +previous:
      Equal.trans(Nat, B.count(O.Item, H.append(Engine.block_items(head), before_items(rest, previous))),
        Nat.add(B.count(O.Item, Engine.block_items(head)), B.count(O.Item, before_items(rest, previous))),
        Nat.add(B.count(O.Item, Engine.block_items(head)), prefix_size(rest, previous)),
        count_append(Engine.block_items(head), before_items(rest, previous)),
        Equal.cong(Nat, Nat, n => Nat.add(B.count(O.Item, Engine.block_items(head)), n),
          B.count(O.Item, before_items(rest, previous)), prefix_size(rest, previous), actual_before_items_have_the_exact_computed_prefix_size(rest, previous)))

law an_actual_block_query_derives_the_exact_before_block_and_after_slices:
  for +blocks: List<&2, Engine.Block>
  for owner: Nat
  for +block: Engine.Block
  for found: {B.query(Engine.Block, blocks, owner) == Some{block} : Maybe<&2, Engine.Block>}
  {flatten(blocks) == H.append(before_items(blocks, owner), H.append(Engine.block_items(block), after_items(blocks, owner))) : List<&2, O.Item>}
def an_actual_block_query_derives_the_exact_before_block_and_after_slices(blocks, owner, block, found):
  match blocks owner:
    case Nil{} owner:
      L.ex_false({Nil{} == H.append(Nil{}, H.append(Engine.block_items(block), Nil{})) : List<&2, O.Item>}, F.none_negative_some(Engine.Block, block, found))
    case Con{+head, +rest} 0n:
      Equal.cong(Engine.Block, List<&2, O.Item>, b => H.append(Engine.block_items(b), flatten(rest)), head, block, F.some_injective(Engine.Block, head, block, found))
    case Con{+head, +rest} 1n+ +previous:
      Equal.trans(List<&2, O.Item>, H.append(Engine.block_items(head), flatten(rest)),
        H.append(Engine.block_items(head), H.append(before_items(rest, previous), H.append(Engine.block_items(block), after_items(rest, previous)))),
        H.append(H.append(Engine.block_items(head), before_items(rest, previous)), H.append(Engine.block_items(block), after_items(rest, previous))),
        Equal.cong(List<&2, O.Item>, List<&2, O.Item>, xs => H.append(Engine.block_items(head), xs), flatten(rest),
          H.append(before_items(rest, previous), H.append(Engine.block_items(block), after_items(rest, previous))),
          an_actual_block_query_derives_the_exact_before_block_and_after_slices(rest, previous, block, found)),
        Equal.sym(List<&2, O.Item>, H.append(H.append(Engine.block_items(head), before_items(rest, previous)), H.append(Engine.block_items(block), after_items(rest, previous))),
          H.append(Engine.block_items(head), H.append(before_items(rest, previous), H.append(Engine.block_items(block), after_items(rest, previous)))),
          append_associative(Engine.block_items(head), before_items(rest, previous), H.append(Engine.block_items(block), after_items(rest, previous)))))


def prefix_item_query_is_retained(+prefix: List<&2, O.Item>, -suffix: List<&2, O.Item>, index: Nat, -item: O.Item,
  found: {B.query(O.Item, prefix, index) == Some{item} : Maybe<&2, O.Item>}) ->
  {B.query(O.Item, H.append(prefix, suffix), index) == Some{item} : Maybe<&2, O.Item>}:
  match prefix index:
    case Nil{} index: L.ex_false({B.query(O.Item, suffix, index) == Some{item} : Maybe<&2, O.Item>}, F.none_negative_some(O.Item, item, found))
    case Con{head, rest} 0n: found
    case Con{head, +rest} 1n+ +previous: prefix_item_query_is_retained(rest, suffix, previous, item, found)


def suffix_item_query_after_prefix(prefix: List<&2, O.Item>, +suffix: List<&2, O.Item>, +index: Nat) ->
  {B.query(O.Item, H.append(prefix, suffix), Nat.add(B.count(O.Item, prefix), index)) == B.query(O.Item, suffix, index) : Maybe<&2, O.Item>}:
  match prefix:
    case Nil{}: {==}
    case Con{head, rest}: suffix_item_query_after_prefix(rest, suffix, index)

law an_actual_block_local_item_query_derives_its_exact_flattened_query:
  for +blocks: List<&2, Engine.Block>
  for owner: Nat
  for +block: Engine.Block
  for +local: Nat
  for -item: O.Item
  for block_found: {B.query(Engine.Block, blocks, owner) == Some{block} : Maybe<&2, Engine.Block>}
  for item_found: {B.query(O.Item, Engine.block_items(block), local) == Some{item} : Maybe<&2, O.Item>}
  {B.query(O.Item, flatten(blocks), Nat.add(prefix_size(blocks, owner), local)) == Some{item} : Maybe<&2, O.Item>}
def an_actual_block_local_item_query_derives_its_exact_flattened_query(blocks, owner, block, local, item, block_found, item_found):
  match blocks owner:
    case Nil{} owner:
      L.ex_false({None{} == Some{item} : Maybe<&2, O.Item>}, F.none_negative_some(Engine.Block, block, block_found))
    case Con{+head, +rest} 0n:
      prefix_item_query_is_retained(Engine.block_items(head), flatten(rest), local, item,
        (%Equal.sym(Engine.Block, head, block, F.some_injective(Engine.Block, head, block, block_found)) :
          {B.query(O.Item, Engine.block_items(_), local) == Some{item} : Maybe<&2, O.Item>} item_found))
    case Con{+head, +rest} 1n+ +previous:
      Equal.trans(Maybe<&2, O.Item>, B.query(O.Item, H.append(Engine.block_items(head), flatten(rest)),
          Nat.add(Nat.add(B.count(O.Item, Engine.block_items(head)), prefix_size(rest, previous)), local)),
        B.query(O.Item, H.append(Engine.block_items(head), flatten(rest)), Nat.add(B.count(O.Item, Engine.block_items(head)), Nat.add(prefix_size(rest, previous), local))),
        Some{item},
        Equal.cong(Nat, Maybe<&2, O.Item>, index => B.query(O.Item, H.append(Engine.block_items(head), flatten(rest)), index),
          Nat.add(Nat.add(B.count(O.Item, Engine.block_items(head)), prefix_size(rest, previous)), local),
          Nat.add(B.count(O.Item, Engine.block_items(head)), Nat.add(prefix_size(rest, previous), local)),
          T.addition_associative(B.count(O.Item, Engine.block_items(head)), prefix_size(rest, previous), local)),
        Equal.trans(Maybe<&2, O.Item>, B.query(O.Item, H.append(Engine.block_items(head), flatten(rest)), Nat.add(B.count(O.Item, Engine.block_items(head)), Nat.add(prefix_size(rest, previous), local))),
          B.query(O.Item, flatten(rest), Nat.add(prefix_size(rest, previous), local)), Some{item},
          suffix_item_query_after_prefix(Engine.block_items(head), flatten(rest), Nat.add(prefix_size(rest, previous), local)),
          an_actual_block_local_item_query_derives_its_exact_flattened_query(rest, previous, block, local, item, block_found, item_found)))


def take_after_prefix(prefix: List<&2, O.Item>, +suffix: List<&2, O.Item>, +local: Nat) ->
  {H.take(Nat.add(B.count(O.Item, prefix), local), H.append(prefix, suffix)) == H.append(prefix, H.take(local, suffix)) : List<&2, O.Item>}:
  match prefix:
    case Nil{}: {==}
    case Con{+head, +rest}:
      Equal.cong(List<&2, O.Item>, List<&2, O.Item>, xs => Con{head, xs}, H.take(Nat.add(B.count(O.Item, rest), local), H.append(rest, suffix)),
        H.append(rest, H.take(local, suffix)), take_after_prefix(rest, suffix, local))


def take_before_actual_local_hit(+prefix: List<&2, O.Item>, +suffix: List<&2, O.Item>, local: Nat, -item: O.Item,
  found: {B.query(O.Item, prefix, local) == Some{item} : Maybe<&2, O.Item>}) ->
  {H.take(local, H.append(prefix, suffix)) == H.take(local, prefix) : List<&2, O.Item>}:
  match prefix local:
    case Nil{} local:
      L.ex_false({H.take(local, suffix) == H.take(local, Nil{}) : List<&2, O.Item>}, F.none_negative_some(O.Item, item, found))
    case Con{head, rest} 0n: {==}
    case Con{+head, +rest} 1n+ +previous:
      Equal.cong(List<&2, O.Item>, List<&2, O.Item>, xs => Con{head, xs}, H.take(previous, H.append(rest, suffix)), H.take(previous, rest),
        take_before_actual_local_hit(rest, suffix, previous, item, found))


def take_decomposed_item_prefix(+prior: List<&2, O.Item>, +block_events: List<&2, O.Item>, +after: List<&2, O.Item>,
  +global: Nat, +local: Nat, -item: O.Item,
  position: {global == Nat.add(B.count(O.Item, prior), local) : Nat},
  found: {B.query(O.Item, block_events, local) == Some{item} : Maybe<&2, O.Item>}) ->
  {H.take(global, H.append(prior, H.append(block_events, after))) == H.append(prior, H.take(local, block_events)) : List<&2, O.Item>}:
  Equal.trans(List<&2, O.Item>, H.take(global, H.append(prior, H.append(block_events, after))),
    H.take(Nat.add(B.count(O.Item, prior), local), H.append(prior, H.append(block_events, after))),
    H.append(prior, H.take(local, block_events)),
    Equal.cong(Nat, List<&2, O.Item>, n => H.take(n, H.append(prior, H.append(block_events, after))), global, Nat.add(B.count(O.Item, prior), local), position),
    Equal.trans(List<&2, O.Item>, H.take(Nat.add(B.count(O.Item, prior), local), H.append(prior, H.append(block_events, after))),
      H.append(prior, H.take(local, H.append(block_events, after))), H.append(prior, H.take(local, block_events)),
      take_after_prefix(prior, H.append(block_events, after), local),
      Equal.cong(List<&2, O.Item>, List<&2, O.Item>, xs => H.append(prior, xs), H.take(local, H.append(block_events, after)), H.take(local, block_events),
        take_before_actual_local_hit(block_events, after, local, item, found))))

law a_located_item_derives_its_exact_prior_block_and_local_item_prefix:
  for +blocks: List<&2, Engine.Block>
  for +owner: Nat
  for +block: Engine.Block
  for +global: Nat
  for +local: Nat
  for -item: O.Item
  for block_found: {B.query(Engine.Block, blocks, owner) == Some{block} : Maybe<&2, Engine.Block>}
  for item_found: {B.query(O.Item, Engine.block_items(block), local) == Some{item} : Maybe<&2, O.Item>}
  for position: {global == Nat.add(prefix_size(blocks, owner), local) : Nat}
  {H.take(global, flatten(blocks)) == H.append(before_items(blocks, owner), H.take(local, Engine.block_items(block))) : List<&2, O.Item>}
def a_located_item_derives_its_exact_prior_block_and_local_item_prefix(blocks, owner, block, global, local, item, block_found, item_found, position):
  Equal.trans(List<&2, O.Item>, H.take(global, flatten(blocks)),
    H.take(global, H.append(before_items(blocks, owner), H.append(Engine.block_items(block), after_items(blocks, owner)))),
    H.append(before_items(blocks, owner), H.take(local, Engine.block_items(block))),
    Equal.cong(List<&2, O.Item>, List<&2, O.Item>, xs => H.take(global, xs), flatten(blocks),
      H.append(before_items(blocks, owner), H.append(Engine.block_items(block), after_items(blocks, owner))),
      an_actual_block_query_derives_the_exact_before_block_and_after_slices(blocks, owner, block, block_found)),
    take_decomposed_item_prefix(before_items(blocks, owner), Engine.block_items(block), after_items(blocks, owner), global, local, item,
      Equal.trans(Nat, global, Nat.add(prefix_size(blocks, owner), local), Nat.add(B.count(O.Item, before_items(blocks, owner)), local), position,
        Equal.cong(Nat, Nat, n => Nat.add(n, local), prefix_size(blocks, owner), B.count(O.Item, before_items(blocks, owner)),
          Equal.sym(Nat, B.count(O.Item, before_items(blocks, owner)), prefix_size(blocks, owner), actual_before_items_have_the_exact_computed_prefix_size(blocks, owner)))), item_found))

# Inverting the actual stamp keeps the exact AuditEvent, including a BoundCore
# origin, and the selected snapshot/reception. Metadata is not filtered out.
def StampedHit(-world: Nat, -input: X.Reception, -selected: D.State, -events: List<&2, O.AuditEvent>, -index: Nat, -item: O.Item) -> Type:
  &event: O.AuditEvent -> L.E<{B.query(O.AuditEvent, events, index) == Some{event} : Maybe<&2, O.AuditEvent>},
    {item == O.Item{world, selected, input, event} : O.Item}>

law every_stamped_item_query_recovers_its_exact_originating_audit_event:
  for +world: Nat
  for +input: X.Reception
  for +selected: D.State
  for +events: List<&2, O.AuditEvent>
  for index: Nat
  for +item: O.Item
  for found: {B.query(O.Item, Engine.stamp(world, input, selected, events), index) == Some{item} : Maybe<&2, O.Item>}
  StampedHit(world, input, selected, events, index, item)
def every_stamped_item_query_recovers_its_exact_originating_audit_event(world, input, selected, events, index, item, found):
  match events index:
    case Nil{} index: L.ex_false(StampedHit(world, input, selected, Nil{}, index, item), F.none_negative_some(O.Item, item, found))
    case Con{+event, rest} 0n:
      (event, L.Both{{==}, Equal.sym(O.Item, O.Item{world, selected, input, event}, item,
        F.some_injective(O.Item, O.Item{world, selected, input, event}, item, found))})
    case Con{head, +rest} 1n+previous:
      every_stamped_item_query_recovers_its_exact_originating_audit_event(world, input, selected, rest, previous, item, found)


def BlockEventHit(block: Engine.Block, -index: Nat, -item: O.Item) -> Type:
  match block:
    case Engine.Block{ordinal, selected, input, before, run}:
      StampedHit(Succ{ordinal}, input, E.database(before), Engine.selected_events(selected, before, C.events(run)), index, item)

law an_actual_block_item_query_recovers_its_same_exact_local_source_event_and_origin:
  for +block: Engine.Block
  for index: Nat
  for +item: O.Item
  for found: {B.query(O.Item, Engine.block_items(block), index) == Some{item} : Maybe<&2, O.Item>}
  BlockEventHit(block, index, item)
def an_actual_block_item_query_recovers_its_same_exact_local_source_event_and_origin(block, index, item, found):
  match block:
    case Engine.Block{+ordinal, +selected, +input, +before, +run}:
      every_stamped_item_query_recovers_its_exact_originating_audit_event(Succ{ordinal}, input, E.database(before),
        Engine.selected_events(selected, before, C.events(run)), index, item, found)


def stamped_world(+world: Nat, -input: X.Reception, -selected: D.State, -events: List<&2, O.AuditEvent>, -index: Nat,
  +item: O.Item, origin: StampedHit(world, input, selected, events, index, item)) -> {Clock.world(item) == world : Nat}:
  match origin:
    case (event, L.Both{found, literal}):
      Equal.cong(O.Item, Nat, Clock.world, item, O.Item{world, selected, input, event}, literal)

law every_actual_local_block_item_has_its_owning_call_world:
  for +block: Engine.Block
  for index: Nat
  for +item: O.Item
  for found: {B.query(O.Item, Engine.block_items(block), index) == Some{item} : Maybe<&2, O.Item>}
  {Clock.world(item) == Engine.world(block) : Nat}
def every_actual_local_block_item_has_its_owning_call_world(block, index, item, found):
  match block:
    case Engine.Block{+ordinal, +selected, +input, +before, +run}:
      stamped_world(Succ{ordinal}, input, E.database(before), Engine.selected_events(selected, before, C.events(run)), index, item,
        every_stamped_item_query_recovers_its_exact_originating_audit_event(Succ{ordinal}, input, E.database(before), Engine.selected_events(selected, before, C.events(run)), index, item, found))

law an_actual_retained_block_local_item_query_recovers_the_same_engine_global_item:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +ordinal: Nat
  for +before: E.Snapshot
  for +owner: Nat
  for +block: Engine.Block
  for +local: Nat
  for -item: O.Item
  for block_found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), owner) == Some{block} : Maybe<&2, Engine.Block>}
  for item_found: {B.query(O.Item, Engine.block_items(block), local) == Some{item} : Maybe<&2, O.Item>}
  {B.query(O.Item, Engine.items(Engine.run(c, binding, public, script, ordinal, before)),
    Nat.add(prefix_size(Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), owner), local)) == Some{item} : Maybe<&2, O.Item>}
def an_actual_retained_block_local_item_query_recovers_the_same_engine_global_item(c, binding, public, script, ordinal, before, owner, block, local, item, block_found, item_found):
  Equal.trans(Maybe<&2, O.Item>, B.query(O.Item, Engine.items(Engine.run(c, binding, public, script, ordinal, before)),
      Nat.add(prefix_size(Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), owner), local)),
    B.query(O.Item, flatten(Engine.blocks(Engine.run(c, binding, public, script, ordinal, before))),
      Nat.add(prefix_size(Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), owner), local)), Some{item},
    Equal.cong(List<&2, O.Item>, Maybe<&2, O.Item>, xs => B.query(O.Item, xs, Nat.add(prefix_size(Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), owner), local)),
      Engine.items(Engine.run(c, binding, public, script, ordinal, before)), flatten(Engine.blocks(Engine.run(c, binding, public, script, ordinal, before))),
      actual_serial_items_are_exactly_the_flattened_actual_retained_blocks(c, binding, public, script, ordinal, before)),
    an_actual_block_local_item_query_derives_its_exact_flattened_query(Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), owner, block, local, item, block_found, item_found))
