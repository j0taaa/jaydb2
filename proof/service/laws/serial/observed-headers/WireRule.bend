# Rule2 for ANY actual observed host WireReceived, with ONLY exact physical
# validity of retained receptions as an IO boundary. Parsed alone does not
# force declared length == actual length; this family is not Processable.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/Decode.bend as Decode
import ../../../model/serial/SerialItems.bend as Items
import ../DecodeReception.bend as Reception
import ../ObservationLocation.bend as Locate
import ../header/History.bend as History
import ./HeaderData.bend as Header
import ./HeaderFact.bend as Fact
import ./BlockLayout.bend as Block
import ./Projection.bend as Projection
import ./Recover.bend as Recover
import ./Site.bend as Site


def PhysicalInputs(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~instance: String) -> Type:
  @owner: Nat -> @block: Engine.Block ->
    {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>} ->
      X.ReceptionValid(Block.input(block))


def at_site(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  -k: String, -x: I.Scenario, -at: Nat, +wire: W.WireRequest, +block: Engine.Block, +item: O.Item, +event: O.AuditEvent,
  scenario: {x == O.scenario(c, item) : I.Scenario},
  exact: {item == O.Item{Engine.world(block), E.database(Chain.block_before(block)), Block.input(block), event} : O.Item},
  received: W.Received(c, Block.input(block), wire)) ->
  E.Rule2(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.WireReceived{wire}, k, x, at):
  %Equal.sym(I.Scenario, x, I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), Block.input(block)},
    Equal.trans(I.Scenario, x, O.scenario(c, item), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), Block.input(block)}, scenario,
      Equal.cong(O.Item, I.Scenario, i => O.scenario(c, i), item, O.Item{Engine.world(block), E.database(Chain.block_before(block)), Block.input(block), event}, exact))) :
    E.Rule2(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.WireReceived{wire}, k, _, at)
  received


def from_seen(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  -k: String, -x: I.Scenario, +at: Nat, +wire: W.WireRequest, +block: Engine.Block, +index: Nat, +item: O.Item, +event: O.AuditEvent,
  scenario: {x == O.scenario(c, item) : I.Scenario}, exact: {item == O.Item{Engine.world(block), E.database(Chain.block_before(block)), Block.input(block), event} : O.Item},
  valid: X.ReceptionValid(Block.input(block)),
  seen: Recover.Seen(Chain.block_before(block), Block.events(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), Block.input(block))), Header.WirePoint{}, index, wire, None{})) ->
  E.Rule2(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.WireReceived{wire}, k, x, at):
  match seen:
    case (+actual_wire, prefix, first, second, tail, L.Both{parsed, L.Both{layout, L.Both{position, L.Both{payload, remaining}}}}):
      at_site(c, binding, public, script, seed, pi, artifacts, instance, k, x, at, wire, block, item, event, scenario, exact,
        Reception.actual_decoding_of_either_wire_kind_derives_received_without_a_reception_encoding_premise(c, E.database(Chain.block_before(block)), Block.input(block), wire, valid,
          Equal.trans(Decode.Decision, Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), Block.input(block))), Decode.Parsed{actual_wire}, Decode.Parsed{wire}, parsed,
            Equal.cong(W.WireRequest, Decode.Decision, w => Decode.Parsed{w}, actual_wire, wire,
              Equal.sym(W.WireRequest, wire, actual_wire,
                Fact.same_wire(Header.WirePoint{}, wire, None{}, actual_wire, D.authenticate(E.database(Chain.block_before(block)), I.credential(W.raw(actual_wire))), payload))))))


def from_site(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  -k: String, -x: I.Scenario, +at: Nat, +wire: W.WireRequest, +block: Engine.Block, +index: Nat, +item: O.Item,
  scenario: {x == O.scenario(c, item) : I.Scenario}, valid: X.ReceptionValid(Block.input(block)),
  hit: Site.Hit(c, block, Header.WirePoint{}, index, item, wire, None{})) ->
  E.Rule2(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.WireReceived{wire}, k, x, at):
  match hit:
    case (+event, L.Both{exact, seen}): from_seen(c, binding, public, script, seed, pi, artifacts, instance, k, x, at, wire, block, index, item, event, scenario, exact, valid, seen)


def from_block(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  -k: String, -x: I.Scenario, +at: Nat, +wire: W.WireRequest, +global: Nat, +item: O.Item,
  physical: PhysicalInputs(c, binding, public, script, seed, instance), scenario: {x == O.scenario(c, item) : I.Scenario},
  relation: O.RelFact(c, binding, public, O.event(item), E.WireReceived{wire}), location: Items.Located(History.blocks(c, binding, public, script, seed, instance), global, item)) ->
  E.Rule2(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.WireReceived{wire}, k, x, at):
  match location:
    case (+owner, +block, +index, L.Both{+block_found, L.Both{item_found, position}}):
      from_site(c, binding, public, script, seed, pi, artifacts, instance, k, x, at, wire, block, index, item, scenario, physical(owner, block, block_found),
        Site.every_actual_header_item_recovers_the_same_job_reception_selected_database_and_exact_header_site(c, binding, public, script, 0n, History.boot(seed, instance), owner, block, Header.WirePoint{}, index, item, wire, None{}, block_found, item_found, relation))


def from_location(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  -k: String, -x: I.Scenario, +at: Nat, +wire: W.WireRequest, physical: PhysicalInputs(c, binding, public, script, seed, instance),
  location: Locate.Located(c, binding, public, script, History.boot(seed, instance), x, at, E.WireReceived{wire})) ->
  E.Rule2(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.WireReceived{wire}, k, x, at):
  match location:
    case (+global, +item, L.Both{time, L.Both{global_found, L.Both{scenario, L.Both{relation, block_location}}}}):
      from_block(c, binding, public, script, seed, pi, artifacts, instance, k, x, at, wire, global, item, physical, scenario, relation, block_location)


def from_projected(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +k: String, -x: I.Scenario, +at: Nat, +wire: W.WireRequest, physical: PhysicalInputs(c, binding, public, script, seed, instance),
  actual: L.E<{k == Source.artifact(binding) : String}, Locate.Located(c, binding, public, script, History.boot(seed, instance), x, at, E.WireReceived{wire})>) ->
  E.Rule2(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.WireReceived{wire}, k, x, at):
  match actual:
    case L.Both{artifact, location}: from_location(c, binding, public, script, seed, pi, artifacts, instance, k, x, at, wire, physical, location)


law every_actual_observed_wire_obeys_rule_two_with_only_exact_physical_validity_of_retained_receptions:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~script: List<&2, Engine.Job>
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~instance: String
  for +k: String
  for -x: I.Scenario
  for +at: Nat
  for +wire: W.WireRequest
  for physical: PhysicalInputs(c, binding, public, script, seed, instance)
  for observed: E.observes(History.environment(c, binding, public, script, seed, pi, artifacts, instance), k, x, at, E.WireReceived{wire})
  E.Rule2(History.environment(c, binding, public, script, seed, pi, artifacts, instance), E.WireReceived{wire}, k, x, at)
def every_actual_observed_wire_obeys_rule_two_with_only_exact_physical_validity_of_retained_receptions(c, binding, public, script, seed, pi, artifacts, instance, k, x, at, wire, physical, observed):
  from_projected(c, binding, public, script, seed, pi, artifacts, instance, k, x, at, wire, physical,
    Projection.every_actual_header_observation_recovers_its_exact_global_item_block_and_unaltered_cofact_relation(c, binding, public, script, seed, pi, artifacts, instance, k, x, at, E.WireReceived{wire}, Unit{}, observed))
