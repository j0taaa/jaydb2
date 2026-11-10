# Every retained block of the concrete source has the checked complete local
# event history. This strengthens whole-source replay for block-local slices;
# the invariant is derived by induction, never supplied by the host.
import Base
import ../../../../contract/Logic.bend as L
import ../../../../contract/Semantics.bend as S
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ./Common.bend as C
import ./Engine.bend as Engine
import ./SerialHistory.bend as History


def All(blocks: List<&2, Engine.Block>) -> Type:
  match blocks:
    case Nil{}: Unit
    case Con{block, rest}: L.E<History.BlockSound(block), All(rest)>


def stopped(+block: Engine.Block, actual: History.BlockSound(block)) -> All(Engine.blocks(Engine.stopped_block(block))):
  Engine.Block{ordinal, selected, input, before, run} = block
  L.Both{actual, Unit{}}


def appended(block: Engine.Block, +suffix: Engine.PrefixRun, actual: History.BlockSound(block), following: All(Engine.blocks(suffix))) ->
  All(Engine.blocks(Engine.append_block(block, suffix))):
  Engine.PrefixRun{blocks, items, snapshot, next, waiting, closed} = suffix
  L.Both{actual, following}


def branch(proceed: Bool, +block: Engine.Block, recur: Nat -> E.Snapshot -> Engine.PrefixRun, actual: History.BlockSound(block),
  following: @ordinal: Nat -> @before: E.Snapshot -> All(Engine.blocks(recur(ordinal, before)))) -> All(Engine.blocks(Engine.branch(proceed, block, recur))):
  match proceed:
    case False{}: stopped(block, actual)
    case True{}: appended(block, recur(Engine.next_after(block), Engine.after(block)), actual, following(Engine.next_after(block), Engine.after(block)))


def executed(+block: Engine.Block, recur: Nat -> E.Snapshot -> Engine.PrefixRun, actual: History.BlockSound(block),
  following: @ordinal: Nat -> @before: E.Snapshot -> All(Engine.blocks(recur(ordinal, before)))) -> All(Engine.blocks(Engine.execute_block(block, recur))):
  Engine.Block{+ordinal, +selected, +input, +before, +run} = block
  branch(C.continues(run), Engine.Block{ordinal, selected, input, before, run}, recur, actual, following)


law actual_serial_engine_derives_the_exact_local_history_of_every_retained_block:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +ordinal: Nat
  for +before: E.Snapshot
  All(Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)))
def actual_serial_engine_derives_the_exact_local_history_of_every_retained_block(c, binding, public, script, ordinal, before):
  match script:
    case Nil{}: Unit{}
    case Con{+job, +rest}:
      executed(Engine.block(c, binding, public, ordinal, before, job),
        n => s => Engine.run(c, binding, public, rest, n, s),
        History.actual_block_sound(c, binding, public, ordinal, before, job),
        n => s => actual_serial_engine_derives_the_exact_local_history_of_every_retained_block(c, binding, public, rest, n, s))
