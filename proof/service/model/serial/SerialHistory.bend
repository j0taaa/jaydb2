# Unbounded induction on the concrete SERIAL dispatcher source. Every
# mutation is replayed immediately, even before pending/fatal cleanup; each
# later call receives the exact paired DB/response/registry from that replay.
# This is an operational model theorem, not a native trace equality premise.
import Base
import ../../../../contract/Logic.bend as L
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../ProtocolService.bend as Q
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../EventObserver.bend as O
import ../EventHistory.bend as T
import ../InvalidationPrefix.bend as Append
import ./Chain.bend as Chain
import ./Common.bend as C
import ./DispatchHistory.bend as Dispatch
import ./Dispatch.bend as NativeDispatch
import ./Engine.bend as Engine
import ./LocalHistory.bend as J


def BlockSound(+block: Engine.Block) -> Type:
  L.E<T.Coherent(Engine.block_items(block), Chain.block_before(block)),
    {T.finish(Engine.block_items(block), Chain.block_before(block)) == Engine.after(block) : E.Snapshot}>


def Sound(+run: Engine.PrefixRun, +before: E.Snapshot) -> Type:
  L.E<T.Coherent(Engine.items(run), before), {T.finish(Engine.items(run), before) == Engine.snapshot(run) : E.Snapshot}>


def selected_sound(selected: Bool, +position: J.Position, +before: E.Snapshot, +run: C.CallRun,
  actual: J.CallSound(position, run, before)) ->
  J.Sound(position, Engine.selected_events(selected, before, C.events(run)), before, C.snapshot(run)):
  match selected:
    case False{}: actual
    case True{}:
      J.quiet_push(position, O.Selection{before}, C.events(run), before, C.snapshot(run), {==}, actual)


def actual_block_sound(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +ordinal: Nat, +before: E.Snapshot, +job: Engine.Job) -> BlockSound(Engine.block(c, binding, public, ordinal, before, job)):
  Engine.Job{+input, +primitives} = job
  selected_sound(Engine.selection(X.decide_reception(c, input)), J.Position{Succ{ordinal}, input, E.database(before)}, before,
    NativeDispatch.run(c, binding, public, before, input, primitives),
    Dispatch.every_actual_dispatch_prefix_derives_its_complete_event_history_and_full_snapshot(c, binding, public, Succ{ordinal}, input, before, primitives))


def append_history_copies(+prefix: List<&2, O.Item>, +suffix: List<&2, O.Item>, +before: E.Snapshot, +middle: E.Snapshot, +after: E.Snapshot,
  coherent: T.Coherent(prefix, before), following: T.Coherent(suffix, middle), final: {T.finish(suffix, middle) == after : E.Snapshot},
  copies: L.E<{T.finish(prefix, before) == middle : E.Snapshot}, {T.finish(prefix, before) == middle : E.Snapshot}>) ->
  L.E<T.Coherent(T.append(prefix, suffix), before), {T.finish(T.append(prefix, suffix), before) == after : E.Snapshot}>:
  match copies:
    case L.Both{for_link, for_finish}:
      L.Both{Append.adjoining_actual_phase_prefixes_preserves_all_local_history_links(prefix, suffix, before, coherent,
        %Equal.sym(E.Snapshot, T.finish(prefix, before), middle, for_link) : T.Coherent(suffix, _) following),
        Equal.trans(E.Snapshot, T.finish(T.append(prefix, suffix), before), T.finish(suffix, T.finish(prefix, before)), after,
          Append.adjoining_phase_prefixes_has_the_exact_sequential_snapshot(prefix, suffix, before),
          Equal.trans(E.Snapshot, T.finish(suffix, T.finish(prefix, before)), T.finish(suffix, middle), after,
            Equal.cong(E.Snapshot, E.Snapshot, state => T.finish(suffix, state), T.finish(prefix, before), middle, for_finish), final))}


def append_history(+prefix: List<&2, O.Item>, +suffix: List<&2, O.Item>, +before: E.Snapshot, +middle: E.Snapshot, +after: E.Snapshot,
  first: L.E<T.Coherent(prefix, before), {T.finish(prefix, before) == middle : E.Snapshot}>,
  later: L.E<T.Coherent(suffix, middle), {T.finish(suffix, middle) == after : E.Snapshot}>) ->
  L.E<T.Coherent(T.append(prefix, suffix), before), {T.finish(T.append(prefix, suffix), before) == after : E.Snapshot}>:
  match first later:
    case L.Both{coherent, finish} L.Both{following, final}:
      append_history_copies(prefix, suffix, before, middle, after, coherent, following, final,
        Q.equality_reopenable(E.Snapshot, T.finish(prefix, before), middle, finish))


def stopped_sound(+block: Engine.Block, actual: BlockSound(block)) -> Sound(Engine.stopped_block(block), Chain.block_before(block)):
  Engine.Block{ordinal, selected, input, before, run} = block
  actual


def appended_sound(+block: Engine.Block, +suffix: Engine.PrefixRun, actual: BlockSound(block), following: Sound(suffix, Engine.after(block))) ->
  Sound(Engine.append_block(block, suffix), Chain.block_before(block)):
  Engine.PrefixRun{blocks, items, snapshot, next, waiting, closed} = suffix
  append_history(Engine.block_items(block), items, Chain.block_before(block), Engine.after(block), snapshot, actual, following)


def branch_sound(proceed: Bool, +block: Engine.Block, recur: Nat -> E.Snapshot -> Engine.PrefixRun, actual: BlockSound(block),
  following: @ordinal: Nat -> @before: E.Snapshot -> Sound(recur(ordinal, before), before)) ->
  Sound(Engine.branch(proceed, block, recur), Chain.block_before(block)):
  match proceed:
    case False{}: stopped_sound(block, actual)
    case True{}: appended_sound(block, recur(Engine.next_after(block), Engine.after(block)), actual, following(Engine.next_after(block), Engine.after(block)))


def executed_sound(+block: Engine.Block, recur: Nat -> E.Snapshot -> Engine.PrefixRun, actual: BlockSound(block),
  following: @ordinal: Nat -> @before: E.Snapshot -> Sound(recur(ordinal, before), before)) ->
  Sound(Engine.execute_block(block, recur), Chain.block_before(block)):
  Engine.Block{+ordinal, +selected, +input, +before, +run} = block
  branch_sound(C.continues(run), Engine.Block{ordinal, selected, input, before, run}, recur, actual, following)


def actual_executed_sound(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +ordinal: Nat, +before: E.Snapshot, +job: Engine.Job, recur: Nat -> E.Snapshot -> Engine.PrefixRun,
  following: @ordinal: Nat -> @before: E.Snapshot -> Sound(recur(ordinal, before), before)) ->
  Sound(Engine.execute_block(Engine.block(c, binding, public, ordinal, before, job), recur), before):
  Engine.Job{+input, +primitives} = job
  executed_sound(Engine.block(c, binding, public, ordinal, before, Engine.Job{input, primitives}), recur,
    actual_block_sound(c, binding, public, ordinal, before, Engine.Job{input, primitives}), following)


law every_actual_serial_prefix_derives_its_complete_mutation_history_and_exact_full_snapshot:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +ordinal: Nat
  for +before: E.Snapshot
  Sound(Engine.run(c, binding, public, script, ordinal, before), before)
def every_actual_serial_prefix_derives_its_complete_mutation_history_and_exact_full_snapshot(c, binding, public, script, ordinal, before):
  match script:
    case Nil{}: L.Both{Unit{}, {==}}
    case Con{+job, +rest}:
      actual_executed_sound(c, binding, public, ordinal, before, job,
        n => s => Engine.run(c, binding, public, rest, n, s),
        n => s => every_actual_serial_prefix_derives_its_complete_mutation_history_and_exact_full_snapshot(c, binding, public, rest, n, s))
