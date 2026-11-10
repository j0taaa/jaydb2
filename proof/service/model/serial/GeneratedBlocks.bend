# Actual retained blocks come from the same indexed script Jobs. No arbitrary
# CallRun, completed outcome or free whole-history source table is accepted.
import Base
import ../../../../contract/Logic.bend as L
import ../../../../contract/Semantics.bend as S
import ../../../Foundations.bend as F
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../FrameBounds.bend as B
import ./Common.bend as C
import ./Engine.bend as Engine
import ./Chain.bend as Chain


def HeadSource(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  -block: Engine.Block, -job: Engine.Job) -> Type:
  {block == Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), job) : Engine.Block}


def IndexedJobs(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  blocks: List<&2, Engine.Block>, script: List<&2, Engine.Job>) -> Type:
  match blocks script:
    case Nil{} script: Unit
    case Con{head, tail} Nil{}: Empty
    case Con{head, tail} Con{job, rest}:
      L.E<HeadSource(c, binding, public, head, job), IndexedJobs(c, binding, public, tail, rest)>


def computed_head(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  ordinal: Nat, before: E.Snapshot, job: Engine.Job) ->
  HeadSource(c, binding, public, Engine.block(c, binding, public, ordinal, before, job), job):
  match job:
    case Engine.Job{input, primitives}: {==}


def stopped_jobs(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  block: Engine.Block, -job: Engine.Job, -rest: List<&2, Engine.Job>, own: HeadSource(c, binding, public, block, job)) ->
  IndexedJobs(c, binding, public, Engine.blocks(Engine.stopped_block(block)), Con{job, rest}):
  match block:
    case Engine.Block{ordinal, selected, input, before, run}: L.Both{own, Unit{}}


def appended_jobs(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +block: Engine.Block, suffix: Engine.PrefixRun, -job: Engine.Job, -rest: List<&2, Engine.Job>,
  own: HeadSource(c, binding, public, block, job), following: IndexedJobs(c, binding, public, Engine.blocks(suffix), rest)) ->
  IndexedJobs(c, binding, public, Engine.blocks(Engine.append_block(block, suffix)), Con{job, rest}):
  match suffix:
    case Engine.PrefixRun{blocks, items, snapshot, next, waiting, closed}: L.Both{own, following}


def branch_jobs(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  proceed: Bool, +block: Engine.Block, -job: Engine.Job, -rest: List<&2, Engine.Job>,
  recur: Nat -> E.Snapshot -> Engine.PrefixRun, own: HeadSource(c, binding, public, block, job),
  following: @ordinal: Nat -> @before: E.Snapshot -> IndexedJobs(c, binding, public, Engine.blocks(recur(ordinal, before)), rest)) ->
  IndexedJobs(c, binding, public, Engine.blocks(Engine.branch(proceed, block, recur)), Con{job, rest}):
  match proceed:
    case False{}: stopped_jobs(c, binding, public, block, job, rest, own)
    case True{}: appended_jobs(c, binding, public, block, recur(Engine.next_after(block), Engine.after(block)), job, rest, own,
      following(Engine.next_after(block), Engine.after(block)))


def executed_jobs(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +block: Engine.Block, -job: Engine.Job, -rest: List<&2, Engine.Job>,
  recur: Nat -> E.Snapshot -> Engine.PrefixRun, own: HeadSource(c, binding, public, block, job),
  following: @ordinal: Nat -> @before: E.Snapshot -> IndexedJobs(c, binding, public, Engine.blocks(recur(ordinal, before)), rest)) ->
  IndexedJobs(c, binding, public, Engine.blocks(Engine.execute_block(block, recur)), Con{job, rest}):
  match block:
    case Engine.Block{+ordinal, +selected, +input, +before, +run}:
      branch_jobs(c, binding, public, C.continues(run), Engine.Block{ordinal, selected, input, before, run}, job, rest, recur, own, following)

law every_actual_retained_block_has_its_same_indexed_script_job_and_computed_dispatch:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +ordinal: Nat
  for +before: E.Snapshot
  IndexedJobs(c, binding, public, Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), script)
def every_actual_retained_block_has_its_same_indexed_script_job_and_computed_dispatch(c, binding, public, script, ordinal, before):
  match script:
    case Nil{}: Unit{}
    case Con{+job, +rest}:
      executed_jobs(c, binding, public, Engine.block(c, binding, public, ordinal, before, job), job, rest,
        n => s => Engine.run(c, binding, public, rest, n, s), computed_head(c, binding, public, ordinal, before, job),
        n => s => every_actual_retained_block_has_its_same_indexed_script_job_and_computed_dispatch(c, binding, public, rest, n, s))


def GeneratedAt(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  -script: List<&2, Engine.Job>, -index: Nat, -block: Engine.Block) -> Type:
  &job: Engine.Job -> L.E<{B.query(Engine.Job, script, index) == Some{job} : Maybe<&2, Engine.Job>}, HeadSource(c, binding, public, block, job)>


def query_indexed_jobs(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +blocks: List<&2, Engine.Block>, +script: List<&2, Engine.Job>, index: Nat, +block: Engine.Block,
  linked: IndexedJobs(c, binding, public, blocks, script),
  found: {B.query(Engine.Block, blocks, index) == Some{block} : Maybe<&2, Engine.Block>}) -> GeneratedAt(c, binding, public, script, index, block):
  match blocks script index linked:
    case Nil{} script index unit:
      L.ex_false(GeneratedAt(c, binding, public, script, index, block), F.none_negative_some(Engine.Block, block, found))
    case Con{head, rest} Nil{} index impossible: L.ex_false(GeneratedAt(c, binding, public, Nil{}, index, block), impossible)
    case Con{+head, rest} Con{job, tail} 0n L.Both{own, later}:
      (job, L.Both{{==}, (%F.some_injective(Engine.Block, head, block, found) : HeadSource(c, binding, public, _, job) own)})
    case Con{head, +rest} Con{job, +tail} 1n+previous L.Both{own, later}:
      query_indexed_jobs(c, binding, public, rest, tail, previous, block, later, found)

law every_actual_block_query_recovers_its_same_actual_script_job_and_computed_dispatch:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +ordinal: Nat
  for +before: E.Snapshot
  for +index: Nat
  for +block: Engine.Block
  for found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), index) == Some{block} : Maybe<&2, Engine.Block>}
  GeneratedAt(c, binding, public, script, index, block)
def every_actual_block_query_recovers_its_same_actual_script_job_and_computed_dispatch(c, binding, public, script, ordinal, before, index, block, found):
  query_indexed_jobs(c, binding, public, Engine.blocks(Engine.run(c, binding, public, script, ordinal, before)), script, index, block,
    every_actual_retained_block_has_its_same_indexed_script_job_and_computed_dispatch(c, binding, public, script, ordinal, before), found)
