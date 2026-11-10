# Concrete finite SERIAL operational prefix. Calls are generated from actual
# decode/dispatch/prepare/invalidate/Core functions, never supplied Item or
# outcome tables. Mathematical prefix exhaustion is not a runtime budget or a
# progress proof. Recovery and the native/IO source simulation remain separate.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Logic.bend as L
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../EventObserver.bend as O
import ../EventHistory.bend as T
import ../FrameBounds.bend as B
import ./Common.bend as C
import ./Dispatch.bend as Dispatch

type Job is Data:
  Job{input: X.Reception, primitives: Dispatch.Primitives}

# No input field chooses a semantic world/call identity. That identity is the
# unbounded number of prior selections, independent of random instance strings
# and the finite diagnostic inspection sequence in Rust.
type Block is Data:
  Block{ordinal: Nat, selected: Bool, input: X.Reception, before: E.Snapshot, run: C.CallRun}

type PrefixRun is Data:
  PrefixRun{blocks: List<&2, Block>, items: List<&2, O.Item>, snapshot: E.Snapshot,
    next_ordinal: Nat, waiting: Bool, closed: Bool}

def items(run: PrefixRun) -> List<&2, O.Item>:
  PrefixRun{blocks, items, snapshot, next, waiting, closed} = run
  items

def blocks(run: PrefixRun) -> List<&2, Block>:
  PrefixRun{blocks, items, snapshot, next, waiting, closed} = run
  blocks

def snapshot(run: PrefixRun) -> E.Snapshot:
  PrefixRun{blocks, items, snapshot, next, waiting, closed} = run
  snapshot

def next_ordinal(run: PrefixRun) -> Nat:
  PrefixRun{blocks, items, snapshot, next, waiting, closed} = run
  next

def selection(disposition: X.Disposition) -> Bool:
  match disposition:
    case X.CloseWithoutResponse{}: False{}
    case X.RefuseClose{status}: False{}
    case _: True{}

def block(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  ordinal: Nat, +before: E.Snapshot, job: Job) -> Block:
  Job{+input, primitives} = job
  Block{ordinal, selection(X.decide_reception(c, input)), input, before, Dispatch.run(c, binding, public, before, input, primitives)}

def world(block: Block) -> Nat:
  Block{ordinal, selected, input, before, run} = block
  Succ{ordinal}

def after(block: Block) -> E.Snapshot:
  Block{ordinal, selected, input, before, run} = block
  C.snapshot(run)

def next(selected: Bool, ordinal: Nat) -> Nat:
  match selected:
    case False{}: ordinal
    case True{}: Succ{ordinal}

def next_after(block: Block) -> Nat:
  Block{ordinal, selected, input, before, run} = block
  next(selected, ordinal)

def selected_events(selected: Bool, before: E.Snapshot, events: List<&2, O.AuditEvent>) -> List<&2, O.AuditEvent>:
  match selected:
    case False{}: events
    case True{}: Con{O.Selection{before}, events}

def stamp(+world: Nat, +input: X.Reception, +selected: D.State, events: List<&2, O.AuditEvent>) -> List<&2, O.Item>:
  match events:
    case Nil{}: Nil{}
    case Con{event, rest}: Con{O.Item{world, selected, input, event}, stamp(world, input, selected, rest)}

def block_items(block: Block) -> List<&2, O.Item>:
  Block{ordinal, selected, input, +before, run} = block
  stamp(Succ{ordinal}, input, E.database(before), selected_events(selected, before, C.events(run)))

def append_block(+block: Block, suffix: PrefixRun) -> PrefixRun:
  PrefixRun{blocks, items, snapshot, next, waiting, closed} = suffix
  PrefixRun{Con{block, blocks}, T.append(block_items(block), items), snapshot, next, waiting, closed}

def stopped_block(+block: Block) -> PrefixRun:
  Block{+ordinal, +selected, +input, +before, +run} = block
  PrefixRun{[Block{ordinal, selected, input, before, run}], block_items(Block{ordinal, selected, input, before, run}),
    C.snapshot(run), next(selected, ordinal), C.waiting(run), C.closed(run)}

def branch(proceed: Bool, +block: Block, recur: Nat -> E.Snapshot -> PrefixRun) -> PrefixRun:
  match proceed:
    case False{}: stopped_block(block)
    case True{}: append_block(block, recur(next_after(block), after(block)))

def execute_block(+block: Block, recur: Nat -> E.Snapshot -> PrefixRun) -> PrefixRun:
  Block{+ordinal, +selected, +input, +before, +run} = block
  branch(C.continues(run), Block{ordinal, selected, input, before, run}, recur)

def run(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  script: List<&2, Job>, +ordinal: Nat, +before: E.Snapshot) -> PrefixRun:
  match script:
    case Nil{}: PrefixRun{Nil{}, Nil{}, before, ordinal, False{}, False{}}
    case Con{job, rest}:
      execute_block(block(c, binding, public, ordinal, before, job),
        next => state => run(c, binding, public, rest, next, state))

law actual_block_ids_are_positive_unbounded_selection_ordinals:
  for -ordinal: Nat
  for -selected: Bool
  for -input: X.Reception
  for -before: E.Snapshot
  for -run: C.CallRun
  {world(Block{ordinal, selected, input, before, run}) == Succ{ordinal} : Nat}
def actual_block_ids_are_positive_unbounded_selection_ordinals(ordinal, selected, input, before, run):
  {==}

law selection_is_the_first_event_of_every_selected_actual_block:
  for -ordinal: Nat
  for -input: X.Reception
  for -before: E.Snapshot
  for -run: C.CallRun
  {B.query(O.Item, block_items(Block{ordinal, True{}, input, before, run}), 0n) ==
    Some{O.Item{Succ{ordinal}, E.database(before), input, O.Selection{before}}} : Maybe<&2, O.Item>}
def selection_is_the_first_event_of_every_selected_actual_block(ordinal, input, before, run):
  {==}
