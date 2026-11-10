# ANY actual prepared-core transaction conclusion satisfies the UNCHANGED
# complete Rule7. ZERO native boundary, Current, completed-outcome, Ready,
# benign-trace, publication or uniqueness premise. Every local source and
# global historical witness is derived from actual Engine observation.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/Semantics.bend as S
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/ObservationUniqueness.bend as U
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../header/History.bend as History
import ../observed-headers/BlockLayout.bend as Block
import ../observed-headers/Audit.bend as Audit
import ../CriticalProjection.bend as Critical
import ../ObservationLocation.bend as Locate
import ./Claim.bend as Claim
import ./BlockSource.bend as Actual
import ./ItemOrigin.bend as Origin
import ./AtSlot.bend as Slot

def for_slot(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +owner: Nat, +block: Engine.Block, +local: Nat, +response: S.Response, +state: D.State, +closes: Bool,
  +found: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +query: {B.query(U.View, U.values(c, binding, public, Engine.block_items(block)), local) == Some{U.ConclusionView{E.Transaction{response}, state, closes}} : Maybe<&2, U.View>}) ->
  E.Rule7(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.PreparedKernel{I.Concluded{response, state, closes}}, Source.artifact(binding),
    I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), Block.input(block)}, O.time(History.position(c, binding, public, script, seed, instance, owner, local))):
  Slot.for_claim(c, binding, public, script, seed, pi, artifacts, instance, owner, block, local, response, state, closes, found, query,
    Claim.any_queried_transaction_conclusion_recovers_its_exact_framing_and_unique_shared_source_slot(c, binding, public,
      Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), Block.events(block), local, response, state, closes,
      (%Audit.block_items(block) : {B.query(U.View, U.values(c, binding, public, _), local) == Some{U.ConclusionView{E.Transaction{response}, state, closes}} : Maybe<&2, U.View>} query),
      Actual.every_actual_retained_block_derives_its_complete_shared_conclusion_shape(c, binding, public, script, 0n, History.boot(seed, instance), owner, block, found)))

def for_local(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  -x: I.Scenario, +at: Nat, +response: S.Response, +state: D.State, +closes: Bool,
  +global: Nat, +item: O.Item, +owner: Nat, +block: Engine.Block, +local: Nat,
  +time: {at == O.time(global) : Nat}, +scenario: {x == O.scenario(c, item) : I.Scenario},
  +found: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +item_query: {B.query(O.Item, Engine.block_items(block), local) == Some{item} : Maybe<&2, O.Item>},
  +position: {global == History.position(c, binding, public, script, seed, instance, owner, local) : Nat},
  relation: O.RelFact(c, binding, public, O.event(item), E.PreparedKernel{I.Concluded{response, state, closes}})) ->
  E.Rule7(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.PreparedKernel{I.Concluded{response, state, closes}}, Source.artifact(binding), x, at):
  %Equal.sym(I.Scenario, x, I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), Block.input(block)},
    Equal.trans(I.Scenario, x, O.scenario(c, item), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), Block.input(block)}, scenario, Origin.scenario(c, block, local, item, item_query))) :
    E.Rule7(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.PreparedKernel{I.Concluded{response, state, closes}}, Source.artifact(binding), _, at)
  %Equal.sym(Nat, at, O.time(History.position(c, binding, public, script, seed, instance, owner, local)),
    Equal.trans(Nat, at, O.time(global), O.time(History.position(c, binding, public, script, seed, instance, owner, local)), time,
      Equal.cong(Nat, Nat, O.time, global, History.position(c, binding, public, script, seed, instance, owner, local), position))) :
    E.Rule7(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.PreparedKernel{I.Concluded{response, state, closes}}, Source.artifact(binding),
      I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), Block.input(block)}, _)
  for_slot(c, binding, public, script, seed, pi, artifacts, instance, owner, block, local, response, state, closes, found,
    Critical.actual_query(c, binding, public, Critical.ConclusionKind{}, Engine.block_items(block), local, item, E.PreparedKernel{I.Concluded{response, state, closes}}, {==}, item_query, relation))

def from_location(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  -x: I.Scenario, +at: Nat, +response: S.Response, +state: D.State, +closes: Bool,
  actual: Locate.Located(c, binding, public, script, History.boot(seed, instance), x, at, E.PreparedKernel{I.Concluded{response, state, closes}})) ->
  E.Rule7(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.PreparedKernel{I.Concluded{response, state, closes}}, Source.artifact(binding), x, at):
  match actual:
    case (+global, +item, L.Both{time, L.Both{global_query, L.Both{scenario, L.Both{relation, (+owner, +block, +local, L.Both{found, L.Both{item_query, position}})}}}}):
      for_local(c, binding, public, script, seed, pi, artifacts, instance, x, at, response, state, closes, global, item, owner, block, local, time, scenario, found, item_query, position, relation)

law every_actual_observed_prepared_transaction_conclusion_obeys_complete_rule7_without_native_or_outcome_assumptions:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~script: List<&2, Engine.Job>
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~instance: String
  for -x: I.Scenario
  for +at: Nat
  for +response: S.Response
  for +state: D.State
  for +closes: Bool
  for observed: E.observes(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Source.artifact(binding), x, at, E.PreparedKernel{I.Concluded{response, state, closes}})
  E.Rule7(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.PreparedKernel{I.Concluded{response, state, closes}}, Source.artifact(binding), x, at)
def every_actual_observed_prepared_transaction_conclusion_obeys_complete_rule7_without_native_or_outcome_assumptions(c, binding, public, script, seed, pi, artifacts, instance, x, at, response, state, closes, observed):
  from_location(c, binding, public, script, seed, pi, artifacts, instance, x, at, response, state, closes,
    Locate.every_relevant_actual_serial_observation_retains_its_exact_item_call_origin_and_all_cofacts(binding, public, c, seed, pi, artifacts, script, instance, x, at,
      E.PreparedKernel{I.Concluded{response, state, closes}}, Unit{}, observed))
