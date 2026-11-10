# Selection ordinals increase for EVERY continuing actual call. They are not
# finite inspection counters, caller IDs or globally unique random strings.
import Base
import ../../../../contract/Logic.bend as L
import ../../../../contract/Semantics.bend as S
import ../../../Foundations.bend as F
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ./Common.bend as C
import ./Engine.bend as Engine
import ./Chain.bend as Chain
import ./Selection.bend as Selection


def selected(block: Engine.Block) -> Bool:
  Engine.Block{ordinal, selected, input, before, run} = block
  selected


def Known(+block: Engine.Block) -> Type:
  L.Disjunction<{selected(block) == True{} : Bool}, {C.continues(Chain.block_run(block)) == False{} : Bool}>


def continuing_was_selected(+block: Engine.Block, known: Known(block),
  continued: {C.continues(Chain.block_run(block)) == True{} : Bool}) -> {selected(block) == True{} : Bool}:
  match known:
    case L.Left{selection}: selection
    case L.Right{terminal}:
      L.ex_false({selected(block) == True{} : Bool}, F.false_negative_true(Equal.trans(Bool, False{}, C.continues(Chain.block_run(block)), True{},
        Equal.sym(Bool, C.continues(Chain.block_run(block)), False{}, terminal), continued)))


def known_actual(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +ordinal: Nat, +before: E.Snapshot, +job: Engine.Job) -> Known(Engine.block(c, binding, public, ordinal, before, job)):
  Engine.Job{input, primitives} = job
  Selection.every_actual_serial_block_is_selected_or_stops_further_selection(c, binding, public, before, input, primitives)


def Names(+ordinal: Nat, blocks: List<&2, Engine.Block>) -> Type:
  match blocks:
    case Nil{}: Unit
    case Con{Engine.Block{actual, selected, input, before, run}, rest}:
      L.E<{actual == ordinal : Nat}, Names(Succ{ordinal}, rest)>


def next_of_selected(+block: Engine.Block, selection: {selected(block) == True{} : Bool}) ->
  {Engine.next_after(block) == Succ{Chain.block_ordinal(block)} : Nat}:
  Engine.Block{ordinal, +selected, input, before, run} = block
  %Equal.sym(Bool, selected, True{}, selection) : {Engine.next(_, ordinal) == Succ{ordinal} : Nat}
  {==}


def stopped_names(block: Engine.Block) -> Names(Chain.block_ordinal(block), Engine.blocks(Engine.stopped_block(block))):
  Engine.Block{ordinal, selected, input, before, run} = block
  L.Both{{==}, Unit{}}


def appended_names(+block: Engine.Block, +suffix: Engine.PrefixRun,
  selection: {selected(block) == True{} : Bool},
  following: Names(Engine.next_after(block), Engine.blocks(suffix))) -> Names(Chain.block_ordinal(block), Engine.blocks(Engine.append_block(block, suffix))):
  Engine.Block{+ordinal, +selected, +input, +before, +run} = block
  Engine.PrefixRun{+blocks, items, snapshot, next, waiting, closed} = suffix
  L.Both{{==}, %next_of_selected(Engine.Block{ordinal, selected, input, before, run}, selection) : Names(_, blocks) following}


def branch_names(proceed: Bool, +block: Engine.Block, recur: Nat -> E.Snapshot -> Engine.PrefixRun,
  same: {C.continues(Chain.block_run(block)) == proceed : Bool}, known: Known(block),
  following: @ordinal: Nat -> @before: E.Snapshot -> Names(ordinal, Engine.blocks(recur(ordinal, before)))) ->
  Names(Chain.block_ordinal(block), Engine.blocks(Engine.branch(proceed, block, recur))):
  match proceed:
    case False{}: stopped_names(block)
    case True{}:
      appended_names(block, recur(Engine.next_after(block), Engine.after(block)), continuing_was_selected(block, known, same),
        following(Engine.next_after(block), Engine.after(block)))


def executed_names(+block: Engine.Block, recur: Nat -> E.Snapshot -> Engine.PrefixRun, known: Known(block),
  following: @ordinal: Nat -> @before: E.Snapshot -> Names(ordinal, Engine.blocks(recur(ordinal, before)))) ->
  Names(Chain.block_ordinal(block), Engine.blocks(Engine.execute_block(block, recur))):
  Engine.Block{+ordinal, +selected, +input, +before, +run} = block
  branch_names(C.continues(run), Engine.Block{ordinal, selected, input, before, run}, recur, {==}, known, following)


def actual_executed_names(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +ordinal: Nat, +before: E.Snapshot, +job: Engine.Job, recur: Nat -> E.Snapshot -> Engine.PrefixRun,
  following: @ordinal: Nat -> @before: E.Snapshot -> Names(ordinal, Engine.blocks(recur(ordinal, before)))) ->
  Names(ordinal, Engine.blocks(Engine.execute_block(Engine.block(c, binding, public, ordinal, before, job), recur))):
  Engine.Job{+input, +primitives} = job
  executed_names(Engine.block(c, binding, public, ordinal, before, Engine.Job{input, primitives}), recur,
    known_actual(c, binding, public, ordinal, before, Engine.Job{input, primitives}), following)


law actual_serial_calls_derive_successive_unbounded_names_without_a_uniqueness_premise:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +ordinal: Nat
  for +before: E.Snapshot
  Names(ordinal, Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)))
def actual_serial_calls_derive_successive_unbounded_names_without_a_uniqueness_premise(c, binding, public, script, ordinal, before):
  match script:
    case Nil{}: Unit{}
    case Con{+job, +rest}:
      actual_executed_names(c, binding, public, ordinal, before, job,
        n => s => Engine.run(c, binding, public, rest, n, s),
        n => s => actual_serial_calls_derive_successive_unbounded_names_without_a_uniqueness_premise(c, binding, public, rest, n, s))
