# Shared notation for the same complete actual serial source; these aliases do
# not project or filter any event, mutation, publication cofact or failure.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/Semantics.bend as S
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/SerialItems.bend as Items


def boot(~seed: Unit -> D.State, ~instance: String) -> E.Snapshot:
  E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}


def blocks(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>, ~seed: Unit -> D.State, ~instance: String) -> List<&2, Engine.Block>:
  Engine.blocks(Engine.run(c, binding, public, script, 0n, boot(seed, instance)))


def items(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>, ~seed: Unit -> D.State, ~instance: String) -> List<&2, O.Item>:
  Engine.items(Engine.run(c, binding, public, script, 0n, boot(seed, instance)))


def environment(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String) -> E.Environment:
  O.environment(binding, public, c, seed, pi, artifacts, items(c, binding, public, script, seed, instance), instance)


def position(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>, ~seed: Unit -> D.State, ~instance: String,
  owner: Nat, local: Nat) -> Nat:
  Nat.add(Items.prefix_size(blocks(c, binding, public, script, seed, instance), owner), local)
