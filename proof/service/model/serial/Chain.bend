# Induction over the ACTUAL serial engine: every later call receives the exact
# prior full snapshot (DB, paired response, instance and registry), and the
# exact computed next selection ordinal. Pending/closed/no-outcome branches
# have no following block. This is not yet semantic event replay or native IO
# correspondence, and grants no Current, validity, certificate or Rule clause.
import Base
import ../../../../contract/Logic.bend as L
import ../../../../contract/Semantics.bend as S
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ./Common.bend as C
import ./Engine.bend as Engine


def block_run(block: Engine.Block) -> C.CallRun:
  Engine.Block{ordinal, selected, input, before, run} = block
  run

def block_ordinal(block: Engine.Block) -> Nat:
  Engine.Block{ordinal, selected, input, before, run} = block
  ordinal

def block_before(block: Engine.Block) -> E.Snapshot:
  Engine.Block{ordinal, selected, input, before, run} = block
  before


def TailAllowed(allowed: Bool, blocks: List<&2, Engine.Block>) -> Type:
  match blocks:
    case Nil{}: Unit
    case Con{head, tail}: {allowed == True{} : Bool}


def Linked(+ordinal: Nat, +previous: E.Snapshot, blocks: List<&2, Engine.Block>) -> Type:
  match blocks:
    case Nil{}: Unit
    case Con{Engine.Block{+actual, +selected, +input, +before, +run}, rest}:
      L.E<{actual == ordinal : Nat}, L.E<{before == previous : E.Snapshot},
        L.E<TailAllowed(C.continues(run), rest), Linked(Engine.next(selected, actual), C.snapshot(run), rest)>>>


def true_tail(blocks: List<&2, Engine.Block>) -> TailAllowed(True{}, blocks):
  match blocks:
    case Nil{}: Unit{}
    case Con{head, tail}: {==}


def appended_link(+block: Engine.Block, +suffix: Engine.PrefixRun,
  continued: {C.continues(block_run(block)) == True{} : Bool},
  following: Linked(Engine.next_after(block), Engine.after(block), Engine.blocks(suffix))) ->
  Linked(block_ordinal(block), block_before(block), Engine.blocks(Engine.append_block(block, suffix))):
  Engine.Block{+ordinal, +selected, input, +before, +run} = block
  Engine.PrefixRun{+blocks, items, snapshot, next, waiting, closed} = suffix
  L.Both{{==}, L.Both{{==}, L.Both{%Equal.sym(Bool, C.continues(run), True{}, continued) : TailAllowed(_, blocks) true_tail(blocks), following}}}


def stopped_link(+block: Engine.Block) ->
  Linked(block_ordinal(block), block_before(block), Engine.blocks(Engine.stopped_block(block))):
  Engine.Block{ordinal, selected, input, before, run} = block
  L.Both{{==}, L.Both{{==}, L.Both{Unit{}, Unit{}}}}


def branch_link(proceed: Bool, +block: Engine.Block,
  recur: Nat -> E.Snapshot -> Engine.PrefixRun,
  same: {C.continues(block_run(block)) == proceed : Bool},
  following: @ordinal: Nat -> @before: E.Snapshot -> Linked(ordinal, before, Engine.blocks(recur(ordinal, before)))) ->
  Linked(block_ordinal(block), block_before(block), Engine.blocks(Engine.branch(proceed, block, recur))):
  match proceed:
    case False{}: stopped_link(block)
    case True{}: appended_link(block, recur(Engine.next_after(block), Engine.after(block)), same, following(Engine.next_after(block), Engine.after(block)))


def executed_link(+block: Engine.Block,
  recur: Nat -> E.Snapshot -> Engine.PrefixRun,
  following: @ordinal: Nat -> @before: E.Snapshot -> Linked(ordinal, before, Engine.blocks(recur(ordinal, before)))) ->
  Linked(block_ordinal(block), block_before(block), Engine.blocks(Engine.execute_block(block, recur))):
  Engine.Block{+ordinal, +selected, +input, +before, +run} = block
  branch_link(C.continues(run), Engine.Block{ordinal, selected, input, before, run}, recur, {==}, following)


def actual_executed_link(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +ordinal: Nat, +before: E.Snapshot, job: Engine.Job,
  recur: Nat -> E.Snapshot -> Engine.PrefixRun,
  following: @ordinal: Nat -> @before: E.Snapshot -> Linked(ordinal, before, Engine.blocks(recur(ordinal, before)))) ->
  Linked(ordinal, before, Engine.blocks(Engine.execute_block(Engine.block(c, binding, public, ordinal, before, job), recur))):
  Engine.Job{input, primitives} = job
  executed_link(Engine.block(c, binding, public, ordinal, before, Engine.Job{input, primitives}), recur, following)


law every_actual_serial_prefix_keeps_exact_state_and_registry_and_selection_links:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +ordinal: Nat
  for +before: E.Snapshot
  Linked(ordinal, before, Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)))
def every_actual_serial_prefix_keeps_exact_state_and_registry_and_selection_links(c, binding, public, script, ordinal, before):
  match script:
    case Nil{}: Unit{}
    case Con{job, +rest}:
      actual_executed_link(c, binding, public, ordinal, before, job,
        n => s => Engine.run(c, binding, public, rest, n, s),
        n => s => every_actual_serial_prefix_keeps_exact_state_and_registry_and_selection_links(c, binding, public, rest, n, s))
