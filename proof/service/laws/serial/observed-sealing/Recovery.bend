# Recover actual decoded preparation and the SAME phase Item query, keeping
# its full original RelFact (including the affine accepted Program). No
# authentication, return tag, owner truth, Current or result is an input.
import Base
import ../../../../../contract/PreparedRegistry.bend as G
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../SourceService.bend as Source
import ../../../../ProtocolService.bend as Q
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/Decode.bend as Decode
import ../../../model/serial/Dispatch.bend as Dispatch
import ../../../model/serial/PreparationPrelude.bend as Prelude
import ../header/History.bend as History
import ../header/PhaseLocation.bend as Location
import ../../../model/serial/GeneratedBlocks.bend as Generated
import ../observed-headers/BlockLayout.bend as Block
import ./SealingData.bend as Data
import ./Observation.bend as Observation
import ./DispatchSites.bend as DispatchSites
import ./ItemSites.bend as Items
import ./PreludeSites.bend as Phase


def Hit(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>, ~seed: Unit -> D.State, ~instance: String,
  -owner: Nat, +block: Engine.Block, -index: Nat, -item: O.Item, -f: E.Fact) -> Type:
  &input: X.Reception -> &primitives: Dispatch.Primitives -> &mode: V.Mode -> &raw: P.Request -> &frames: List<&2, Q.Frame> ->
    L.E<{B.query(Engine.Job, script, owner) == Some{Engine.Job{input, primitives}} : Maybe<&2, Engine.Job>},
      L.E<{Decode.run(c, E.database(Chain.block_before(block)), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames} : Decode.DecodeRun},
        L.E<Phase.Hit(Engine.world(block), input, Chain.block_before(block), frames, V.run(c, mode, raw, Chain.block_before(block), Prelude.returns(primitives)), index, item),
          O.RelFact(c, binding, public, O.event(item), f)>>>


def input_equal(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives,
  source: Generated.HeadSource(c, binding, public, block, Engine.Job{input, primitives})) -> {Block.input(block) == input : X.Reception}:
  Equal.cong(Engine.Block, X.Reception, Block.input, block, Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives}), source)


def parsed_input(~c: S.Configuration, +before: E.Snapshot, +actual: X.Reception, +input: X.Reception, +wire: W.WireRequest,
  equal: {actual == input : X.Reception}, parsed: {Decode.decision(Decode.run(c, E.database(before), actual)) == Decode.Parsed{wire} : Decode.Decision}) ->
  {Decode.decision(Decode.run(c, E.database(before), input)) == Decode.Parsed{wire} : Decode.Decision}:
  Equal.trans(Decode.Decision, Decode.decision(Decode.run(c, E.database(before), input)), Decode.decision(Decode.run(c, E.database(before), actual)), Decode.Parsed{wire},
    Equal.sym(Decode.Decision, Decode.decision(Decode.run(c, E.database(before), actual)), Decode.decision(Decode.run(c, E.database(before), input)),
      Equal.cong(X.Reception, Decode.Decision, i => Decode.decision(Decode.run(c, E.database(before), i)), actual, input, equal)), parsed)


def decoded_from_parsed(+run: Decode.DecodeRun, +wire: W.WireRequest, parsed: {Decode.decision(run) == Decode.Parsed{wire} : Decode.Decision}) ->
  {run == Decode.DecodeRun{Decode.Parsed{wire}, Decode.frames(run)} : Decode.DecodeRun}:
  match run:
    case Decode.DecodeRun{+decision, +frames}:
      Equal.cong(Decode.Decision, Decode.DecodeRun, d => Decode.DecodeRun{d, frames}, decision, Decode.Parsed{wire}, parsed)


def event_relevant(+item: O.Item, -f: E.Fact, relevant: Data.Relevant(Data.fact(f)), equal: {Data.event(O.event(item)) == Data.fact(f) : Data.View}) -> Data.Relevant(Data.event(O.event(item))):
  %Equal.sym(Data.View, Data.event(O.event(item)), Data.fact(f), equal) : Data.Relevant(_)
  relevant


def phase_source_query(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>, ~seed: Unit -> D.State, ~instance: String,
  +owner: Nat, +block: Engine.Block, +index: Nat, +item: O.Item, +input: X.Reception, +primitives: Dispatch.Primitives, +mode: V.Mode, +raw: P.Request, +frames: List<&2, Q.Frame>,
  block_found: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  job_found: {B.query(Engine.Job, script, owner) == Some{Engine.Job{input, primitives}} : Maybe<&2, Engine.Job>},
  decoded: {Decode.run(c, E.database(Chain.block_before(block)), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames} : Decode.DecodeRun},
  item_found: {B.query(O.Item, Engine.block_items(block), index) == Some{item} : Maybe<&2, O.Item>}) ->
  {B.query(O.Item, Prelude.source(c, Engine.world(block), input, Chain.block_before(block), mode, raw, Prelude.returns(primitives), frames), index) == Some{item} : Maybe<&2, O.Item>}:
  Equal.trans(Maybe<&2, O.Item>, B.query(O.Item, Prelude.source(c, Engine.world(block), input, Chain.block_before(block), mode, raw, Prelude.returns(primitives), frames), index), B.query(O.Item, Engine.block_items(block), index), Some{item},
    Equal.cong(List<&2, O.Item>, Maybe<&2, O.Item>, xs => B.query(O.Item, xs, index), Prelude.source(c, Engine.world(block), input, Chain.block_before(block), mode, raw, Prelude.returns(primitives), frames), Engine.block_items(block),
      Equal.sym(List<&2, O.Item>, Engine.block_items(block), Prelude.source(c, Engine.world(block), input, Chain.block_before(block), mode, raw, Prelude.returns(primitives), frames),
        Location.an_actual_preparation_block_recovers_its_exact_codec_and_phase_source_from_its_same_script_job(c, binding, public, script, 0n, History.boot(seed, instance), owner, block, input, primitives, mode, raw, frames, block_found, job_found, decoded))), item_found)


def with_relations(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>, ~seed: Unit -> D.State, ~instance: String,
  +owner: Nat, +block: Engine.Block, +index: Nat, +item: O.Item, -f: E.Fact, +input: X.Reception, +primitives: Dispatch.Primitives, +mode: V.Mode, +raw: P.Request, +frames: List<&2, Q.Frame>,
  +block_found: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +job_found: {B.query(Engine.Job, script, owner) == Some{Engine.Job{input, primitives}} : Maybe<&2, Engine.Job>},
  +decoded: {Decode.run(c, E.database(Chain.block_before(block)), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames} : Decode.DecodeRun},
  item_found: {B.query(O.Item, Engine.block_items(block), index) == Some{item} : Maybe<&2, O.Item>},
  first_relevant: Data.Relevant(Data.fact(f)), second_relevant: Data.Relevant(Data.fact(f)),
  relations: L.E<O.RelFact(c, binding, public, O.event(item), f), O.RelFact(c, binding, public, O.event(item), f)>) -> Hit(c, binding, public, script, seed, instance, owner, block, index, item, f):
  match relations:
    case L.Both{first, second}:
      (input, primitives, mode, raw, frames, L.Both{job_found, L.Both{decoded, L.Both{
        Phase.query(Engine.world(block), input, Chain.block_before(block), raw, frames, V.run(c, mode, raw, Chain.block_before(block), Prelude.returns(primitives)), index, item,
          event_relevant(item, f, second_relevant, Observation.actual_event_view(c, binding, public, O.event(item), f, first_relevant, first)),
          phase_source_query(c, binding, public, script, seed, instance, owner, block, index, item, input, primitives, mode, raw, frames, block_found, job_found, decoded, item_found)), second}}})


def with_decoded(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>, ~seed: Unit -> D.State, ~instance: String,
  +owner: Nat, +block: Engine.Block, +index: Nat, +item: O.Item, -f: E.Fact, +input: X.Reception, +primitives: Dispatch.Primitives, +mode: V.Mode, +raw: P.Request, +frames: List<&2, Q.Frame>,
  +block_found: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +job_found: {B.query(Engine.Job, script, owner) == Some{Engine.Job{input, primitives}} : Maybe<&2, Engine.Job>},
  +decoded: {Decode.run(c, E.database(Chain.block_before(block)), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames} : Decode.DecodeRun},
  item_found: {B.query(O.Item, Engine.block_items(block), index) == Some{item} : Maybe<&2, O.Item>},
  relevance: L.E<Data.Relevant(Data.fact(f)), L.E<Data.Relevant(Data.fact(f)), Data.Relevant(Data.fact(f))>>,
  relation: O.RelFact(c, binding, public, O.event(item), f)) -> Hit(c, binding, public, script, seed, instance, owner, block, index, item, f):
  match relevance:
    case L.Both{first, L.Both{second, third}}:
      with_relations(c, binding, public, script, seed, instance, owner, block, index, item, f, input, primitives, mode, raw, frames, block_found, job_found, decoded, item_found, second, third,
        Observation.duplicate_relevant_actual_relation(c, binding, public, O.event(item), f, first, relation))


def from_parsed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>, ~seed: Unit -> D.State, ~instance: String,
  +owner: Nat, +block: Engine.Block, +index: Nat, +item: O.Item, -f: E.Fact, +input: X.Reception, +primitives: Dispatch.Primitives, +mode: V.Mode, +raw: P.Request,
  +block_found: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +job_found: {B.query(Engine.Job, script, owner) == Some{Engine.Job{input, primitives}} : Maybe<&2, Engine.Job>},
  item_found: {B.query(O.Item, Engine.block_items(block), index) == Some{item} : Maybe<&2, O.Item>},
  source: Generated.HeadSource(c, binding, public, block, Engine.Job{input, primitives}),
  parsed: {Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), Block.input(block))) == Decode.Parsed{W.Extension{V.operation(mode), raw}} : Decode.Decision},
  relevance: L.E<Data.Relevant(Data.fact(f)), L.E<Data.Relevant(Data.fact(f)), Data.Relevant(Data.fact(f))>>,
  relation: O.RelFact(c, binding, public, O.event(item), f)) -> Hit(c, binding, public, script, seed, instance, owner, block, index, item, f):
  with_decoded(c, binding, public, script, seed, instance, owner, block, index, item, f, input, primitives, mode, raw, Decode.frames(Decode.run(c, E.database(Chain.block_before(block)), input)), block_found, job_found,
    decoded_from_parsed(Decode.run(c, E.database(Chain.block_before(block)), input), W.Extension{V.operation(mode), raw},
      parsed_input(c, Chain.block_before(block), Block.input(block), input, W.Extension{V.operation(mode), raw}, input_equal(c, binding, public, block, input, primitives, source), parsed)), item_found, relevance, relation)



def sealed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>, ~seed: Unit -> D.State, ~instance: String,
  +owner: Nat, +block: Engine.Block, +index: Nat, +item: O.Item, +entry: G.Entry, -program: S.Program,
  block_found: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  item_found: {B.query(O.Item, Engine.block_items(block), index) == Some{item} : Maybe<&2, O.Item>},
  hit: Items.Hit(c, binding, public, script, owner, block, index, item, E.ArtifactSealed{entry, program})) -> Hit(c, binding, public, script, seed, instance, owner, block, index, item, E.ArtifactSealed{entry, program}):
  match hit:
    case (+event, L.Both{+exact, L.Both{relation, (+input, +primitives, L.Both{job_found, L.Both{source, DispatchSites.PreparationCause{+mode, +raw, parsed, cause}}})}}):
      from_parsed(c, binding, public, script, seed, instance, owner, block, index, item, E.ArtifactSealed{entry, program}, input, primitives, mode, raw, block_found, job_found, item_found, source, parsed,
        L.Both{Unit{}, L.Both{Unit{}, Unit{}}},
        (%Equal.sym(O.AuditEvent, O.event(item), event, Equal.cong(O.Item, O.AuditEvent, O.event, item, O.Item{Engine.world(block), E.database(Chain.block_before(block)), Block.input(block), event}, exact)) : O.RelFact(c, binding, public, _, E.ArtifactSealed{entry, program}) relation))
