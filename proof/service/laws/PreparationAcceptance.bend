# Concrete preparation Rule4 over the full chronological observer. Current,
# identity observations and original logical judgments are derived separately;
# neither the target rule nor a selected valid/final state is a primitive.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Protocol.bend as P
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../SourceService.bend as Source
import ../../HostTransitions.bend as Host
import ../specification/ServiceLaws.bend as E
import ../phases/PreparePhases.bend as V
import ../model/EventObserver.bend as O
import ../model/PreparationCurrent.bend as A
import ../model/PreparationPrefix.bend as Prefix
import ../model/FrameBounds.bend as B
import ./PreparationJudgments.bend as J

def environment(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  ~world: Nat, ~input: X.Reception, ~mode: V.Mode, ~raw: P.Request, ~returns: V.Returns) -> E.Environment:
  O.environment(binding, public, c, seed, pi, artifacts,
    A.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw, returns), instance)

def identity_from_queries(~c: S.Configuration, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot,
  +returns: V.Returns, +context: D.Context,
  authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  queries: L.E<{B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, returns)), 0n) ==
      Some{V.WireReceived{W.Extension{V.operation(mode), raw}}} : Maybe<&2, V.PreparationEvent>},
    {B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, returns)), 1n) ==
      Some{V.IdentityEstablished{W.Extension{V.operation(mode), raw}, D.authenticate(E.database(before), I.credential(raw))}} : Maybe<&2, V.PreparationEvent>}>) ->
  {B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, returns)), 1n) ==
    Some{V.IdentityEstablished{W.Extension{V.operation(mode), raw}, Some{context}}} : Maybe<&2, V.PreparationEvent>}:
  match queries:
    case L.Both{wire, identity}:
      Equal.trans(Maybe<&2, V.PreparationEvent>,
        B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, returns)), 1n),
        Some{V.IdentityEstablished{W.Extension{V.operation(mode), raw}, D.authenticate(E.database(before), I.credential(raw))}},
        Some{V.IdentityEstablished{W.Extension{V.operation(mode), raw}, Some{context}}}, identity,
        Equal.cong(Maybe<&2, D.Context>, Maybe<&2, V.PreparationEvent>,
          identity => Some{V.IdentityEstablished{W.Extension{V.operation(mode), raw}, identity}},
          D.authenticate(E.database(before), I.credential(raw)), Some{context}, authenticated))

def earlier_identity(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  ~world: Nat, ~input: X.Reception, ~mode: V.Mode, ~raw: P.Request, ~returns: V.Returns, ~context: D.Context,
  authenticated: {D.authenticate(seed(Unit{}), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}) ->
  E.Before(environment(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, returns),
    Source.artifact(binding), I.Serve{world, c, seed(Unit{}), input}, 6n,
    E.IdentityEstablished{W.Extension{V.operation(mode), raw}, Some{context}}):
  Prefix.a_real_earlier_query_constructs_the_exact_full_before_fact(binding, public, c, seed, pi, artifacts,
    A.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw, returns), instance,
    2n, O.Item{world, seed(Unit{}), input, O.Preparation{V.IdentityEstablished{W.Extension{V.operation(mode), raw}, Some{context}}}}, 6n,
    Prefix.exact_dispatcher_phase_query_supplies_the_actual_observer_query(c, world, input,
      E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw, returns, 1n,
      V.IdentityEstablished{W.Extension{V.operation(mode), raw}, Some{context}},
      identity_from_queries(c, mode, raw, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, returns, context, authenticated,
        Prefix.actual_dispatcher_has_the_exact_wire_and_identity_queries(c, mode, raw, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, returns))), {==})

def pack_acceptance(~a: E.Environment, -k: String, -world: Nat, -c: S.Configuration, -state: D.State,
  -input: X.Reception, -time: Nat, -operation: W.Operation, -raw: P.Request, -context: D.Context, -program: S.Program,
  +snapshot: E.Snapshot,
  current: E.Current(a, k, I.Serve{world, c, state, input}, time, snapshot),
  selected_state: E.SnapshotForCall(I.Serve{world, c, state, input}, snapshot),
  identity: E.Before(a, k, I.Serve{world, c, state, input}, time, E.IdentityEstablished{W.Extension{operation, raw}, Some{context}}),
  received: W.Received(c, input, W.Extension{operation, raw}),
  payload: J.Payload(E.core_environment(True{}, a), c, operation, raw, program)) ->
  E.PreparationAccepted(a, k, I.Serve{world, c, state, input}, time, W.Extension{operation, raw}, context, program):
  match payload:
    case L.Both{admission, L.Both{universal, read}}:
      (snapshot, L.Both{current, L.Both{selected_state, L.Both{identity,
        L.Both{received, L.Both{admission, L.Both{universal, read}}}}}})

law actual_preparation_acceptance_obeys_the_full_chronological_rule:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~instance: String
  for ~world: Nat
  for ~input: X.Reception
  for ~mode: V.Mode
  for ~raw: P.Request
  for ~allocation: V.AllocatorReturn
  for ~seal: V.SealReturn
  for ~send: V.SendReturn
  for ~context: D.Context
  for authenticated: {D.authenticate(seed(Unit{}), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}
  for received: W.Received(c, input, W.Extension{V.operation(mode), raw})
  for checked: Host.PreparationChecked(binding, c, public, raw, V.read_only(mode))
  E.PreparationAccepted(environment(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw,
      V.Returns{V.CheckerAccepted{}, allocation, seal, send}), Source.artifact(binding),
    I.Serve{world, c, seed(Unit{}), input}, 6n, W.Extension{V.operation(mode), raw}, context,
    Source.program(binding, Host.origin(public, I.code(raw))))
def actual_preparation_acceptance_obeys_the_full_chronological_rule(binding, public, c, seed, pi, artifacts, instance,
  world, input, mode, raw, allocation, seal, send, context, authenticated, received, checked):
  pack_acceptance(environment(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw,
      V.Returns{V.CheckerAccepted{}, allocation, seal, send}), Source.artifact(binding), world, c, seed(Unit{}), input, 6n,
    V.operation(mode), raw, context, Source.program(binding, Host.origin(public, I.code(raw))),
    E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}},
    Prefix.every_actual_early_preparation_prefix_has_full_current_history(binding, public, c, seed, pi, artifacts,
      instance, world, input, mode, raw, V.Returns{V.CheckerAccepted{}, allocation, seal, send}, 3n, {==}), {==},
    earlier_identity(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw,
      V.Returns{V.CheckerAccepted{}, allocation, seal, send}, context, authenticated), received,
    J.the_same_original_judgments_hold_for_the_full_operational_observer(binding, public, c, seed, pi, artifacts,
      A.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
        V.Returns{V.CheckerAccepted{}, allocation, seal, send}), instance, mode, raw, checked))
