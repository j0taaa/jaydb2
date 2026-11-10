# Concrete serial source -> COMPLETE Current at every actual prefix, while the
# full later suffix remains in the observer. Initialization here is FRESH;
# recovery, native-source simulation, lawful admission and progress are separate.
# No Current, desired observer trace or final invariant is an input premise.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Logic.bend as L
import ../../../../contract/PreparedLaws.bend as H
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../CurrentWitness.bend as Current
import ../EventObserver.bend as O
import ../EventHistory.bend as T
import ../FrameBounds.bend as B
import ./Engine.bend as Engine
import ./SerialHistory.bend as History


def history_coherent(+run: Engine.PrefixRun, +before: E.Snapshot, proof: History.Sound(run, before)) -> T.Coherent(Engine.items(run), before):
  match proof:
    case L.Both{coherent, final}: coherent


def prefix_coherent(+count: Nat, +items: List<&2, O.Item>, +before: E.Snapshot, actual: T.Coherent(items, before)) -> T.Coherent(T.take(count, items), before):
  match count items actual:
    case 0n _ _: Unit{}
    case 1n+k Nil{} _: Unit{}
    case 1n+k Con{+item, +rest} L.Both{head, later}:
      L.Both{head, prefix_coherent(k, rest, T.next(O.change(O.event(item)), before), later)}


def source(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  script: List<&2, Engine.Job>, before: E.Snapshot) -> List<&2, O.Item>:
  Engine.items(Engine.run(c, binding, public, script, 0n, before))


def at_prefix(+count: Nat, items: List<&2, O.Item>) -> Nat:
  O.time(B.count(O.Item, T.take(count, items)))


def after_prefix(count: Nat, items: List<&2, O.Item>, before: E.Snapshot) -> E.Snapshot:
  T.finish(T.take(count, items), before)

# Current depends on a serving scenario's configuration and execution/run
# group, not its initial selected DB field. Observations themselves are NEVER
# reselected or erased; this is merely definitional scenario indexing of Current.
def current_same_call_group(~a: E.Environment, ~c: S.Configuration, -k: String, -world: Nat,
  -input: X.Reception, -old_selected: D.State, -selected: D.State, -time: Nat, -snapshot: E.Snapshot,
  actual: E.Current(a, k, I.Serve{world, c, old_selected, input}, time, snapshot)) ->
  E.Current(a, k, I.Serve{world, c, selected, input}, time, snapshot):
  actual


law actual_serial_history_derives_complete_current_at_every_internal_prefix:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~script: List<&2, Engine.Job>
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~instance: String
  for -world: Nat
  for -input: X.Reception
  for -selected: D.State
  for +count: Nat
  E.Current(O.environment(binding, public, c, seed, pi, artifacts,
      source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), instance), Source.artifact(binding),
    I.Serve{world, c, selected, input},
    at_prefix(count, source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})),
    after_prefix(count, source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}))
def actual_serial_history_derives_complete_current_at_every_internal_prefix(c, binding, public, script, seed, pi, artifacts, instance, world, input, selected, count):
  current_same_call_group(O.environment(binding, public, c, seed, pi, artifacts,
      source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), instance), c, Source.artifact(binding), world, input,
    E.database(after_prefix(count, source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})),
    selected, at_prefix(count, source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})),
    after_prefix(count, source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}),
    Current.complete_current_is_derived_from_the_lossless_operational_event_prefix(binding, public, c, seed, pi, artifacts,
      source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), instance,
      T.take(count, source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})),
      T.drop(count, source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), world, input,
      prefix_coherent(count, source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}},
        history_coherent(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}},
          History.every_actual_serial_prefix_derives_its_complete_mutation_history_and_exact_full_snapshot(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}))),
      Equal.sym(List<&2, O.Item>,
        T.append(T.take(count, source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), T.drop(count, source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}))),
        source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}),
        T.taking_a_prefix_preserves_every_event_in_its_full_suffix(count, source(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})))))
