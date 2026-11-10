# Complete unchanged Concluded Rule7 at an actual retained block slot. Local
# occurrence evidence and closing are DERIVED by the final observed theorem.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/LAWS.bend as K
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/Semantics.bend as S
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/ObservationUniqueness.bend as U
import ../../../model/PreparationPrefix.bend as Prefix
import ../../../model/TimeEmbedding.bend as Time
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/SerialItems.bend as Items
import ../header/History.bend as History
import ../../../model/serial/GeneratedBlocks.bend as Generated
import ../observed-headers/BlockLayout.bend as Block
import ../observed-headers/Audit.bend as Audit
import ../ConclusionUniqueness.bend as Unique
import ./Meaning.bend as M
import ./Projection.bend as Projection
import ./Claim.bend as Claim
import ./Closing.bend as Closing

def prepared_before(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +owner: Nat, +block: Engine.Block, +local: Nat, +response: S.Response, +bytes: List<&2, U32>, +prepared_at: Nat, +event: O.AuditEvent,
  found: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  query: {B.query(O.AuditEvent, Block.events(block), prepared_at) == Some{event} : Maybe<&2, O.AuditEvent>},
  ordered: {Nat.is_lt(prepared_at, local) == True{} : Bool}, payload: {M.prepared(event) == Some{M.Framing{response, bytes}} : Maybe<&2, M.Framing>}) ->
  E.PreparedBefore(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Source.artifact(binding),
    I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), Block.input(block)}, O.time(History.position(c, binding, public, script, seed, instance, owner, local)), E.Transaction{response}, bytes):
  %Projection.event_prepared(c, binding, public, event, response, bytes, payload) :
    E.Before(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Source.artifact(binding),
      I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), Block.input(block)}, O.time(History.position(c, binding, public, script, seed, instance, owner, local)), _)
  Prefix.a_real_earlier_query_constructs_the_exact_full_before_fact(binding, public, c, seed, pi, artifacts, History.items(c, binding, public, script, seed, instance), instance,
    History.position(c, binding, public, script, seed, instance, owner, prepared_at), O.Item{Engine.world(block), E.database(Chain.block_before(block)), Block.input(block), event},
    O.time(History.position(c, binding, public, script, seed, instance, owner, local)),
    Items.an_actual_retained_block_local_item_query_recovers_the_same_engine_global_item(c, binding, public, script, 0n, History.boot(seed, instance), owner, block, prepared_at,
      O.Item{Engine.world(block), E.database(Chain.block_before(block)), Block.input(block), event}, found, Audit.block_query(block, prepared_at, event, query)),
    Time.adding_prefix_preserves_strict_order(Items.prefix_size(History.blocks(c, binding, public, script, seed, instance), owner), prepared_at, local, ordered))

def closing(~a: E.Environment, -k: String, -x: I.Scenario, -at: Nat, +closes: Bool,
  same: {closes == False{} : Bool}, correct: I.ClosingCorrect(x, False{})) ->
  L.E<K.ClosingAllowed(E.core_environment(True{}, a), k, x, at, closes), K.CloseEventually(closes, E.core_environment(True{}, a), k, x)>:
  %Equal.sym(Bool, closes, False{}, same) : L.E<K.ClosingAllowed(E.core_environment(True{}, a), k, x, at, _), K.CloseEventually(_, E.core_environment(True{}, a), k, x)>
  L.Both{L.Left{correct}, Unit{}}

def for_claim(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +owner: Nat, +block: Engine.Block, +local: Nat, +response: S.Response, +state: D.State, +closes: Bool,
  +found: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +query: {B.query(U.View, U.values(c, binding, public, Engine.block_items(block)), local) == Some{U.ConclusionView{E.Transaction{response}, state, closes}} : Maybe<&2, U.View>},
  claim: Claim.Claim(c, binding, public, Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), Block.events(block), local, response, state, closes)) ->
  E.Rule7(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.PreparedKernel{I.Concluded{response, state, closes}}, Source.artifact(binding),
    I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), Block.input(block)}, O.time(History.position(c, binding, public, script, seed, instance, owner, local))):
  match claim:
    case L.Both{same, (+bytes, +prepared_at, +event, L.Both{ordered, L.Both{prepared_query, L.Both{payload, unique}}})}:
      L.Both{(bytes, prepared_before(c, binding, public, script, seed, pi, artifacts, instance, owner, block, local, response, bytes, prepared_at, event, found, prepared_query, ordered, payload)),
        L.Both{closing(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Source.artifact(binding),
            I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), Block.input(block)}, O.time(History.position(c, binding, public, script, seed, instance, owner, local)), closes, same,
            Closing.from_generated(c, binding, public, script, owner, block, local, response, state, closes, query,
              Generated.every_actual_block_query_recovers_its_same_actual_script_job_and_computed_dispatch(c, binding, public, script, 0n, History.boot(seed, instance), owner, block, found))),
          Unique.from_actual_local_source(binding, public, c, seed, pi, artifacts, script, instance,
            I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), Block.input(block)}, owner, block, local, E.Transaction{response}, state, closes, found, {==},
            (%Equal.sym(List<&2, O.Item>, Engine.block_items(block), Engine.stamp(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), Block.events(block)), Audit.block_items(block)) :
              U.OnlyTag(3n, U.values(c, binding, public, _), local, U.ConclusionView{E.Transaction{response}, state, closes}) unique))}}
