# Complete-source inversion for actual single-call preparation. No uniqueness,
# no-publication or final database law is supplied as a primitive premise.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/LAWS.bend as K
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Protocol.bend as P
import ../../../contract/Requirements.bend as R
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../SourceService.bend as Source
import ../specification/ServiceLaws.bend as E
import ../phases/PreparePhases.bend as V
import ../phases/PrepareEvents.bend as A
import ./EventObserver.bend as O
import ./PreparationCurrent.bend as PSource
import ./ObservationUniqueness.bend as U
import ./ObservedHistory.bend as Equations

def phase_other_kinds(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, phase: V.PreparationEvent) ->
  L.E<{Nat.is_eq(U.tag(U.view(V.fact(c, binding, public, phase))), 1n) == False{} : Bool},
    {Nat.is_eq(U.tag(U.view(V.fact(c, binding, public, phase))), 4n) == False{} : Bool}>:
  match phase:
    case V.WireReceived{wire}: L.Both{{==}, {==}}
    case V.IdentityEstablished{wire, context}: L.Both{{==}, {==}}
    case V.Accepted{wire, context}: L.Both{{==}, {==}}
    case V.Refuted{wire, context}: L.Both{{==}, {==}}
    case V.PrimitiveFailed{stage, id, fatal}: L.Both{{==}, {==}}
    case V.HandleChosen{handle}: L.Both{{==}, {==}}
    case V.ReceiptPrepared{receipt, bytes}: L.Both{{==}, {==}}
    case V.ArtifactSealed{entry}: L.Both{{==}, {==}}
    case V.RegistryChanged{entry, before, after}: L.Both{{==}, {==}}
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: L.Both{{==}, {==}}
    case V.ErrorPrepared{status, bytes}: L.Both{{==}, {==}}
    case V.ErrorConcluded{status, snapshot, closes}: L.Both{{==}, {==}}
    case V.Delivered{bytes}: L.Both{{==}, {==}}
    case V.Interrupted{prefix}: L.Both{{==}, {==}}
    case V.Closed{}: L.Both{{==}, {==}}

def first(-A: Type, -B: Type, pair: L.E<A, B>) -> A:
  match pair:
    case L.Both{a, b}: a

def second(-A: Type, -B: Type, pair: L.E<A, B>) -> B:
  match pair:
    case L.Both{a, b}: b

def no_selection_phases(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +selected: D.State, +input: X.Reception, phases: List<&2, V.PreparationEvent>) ->
  U.NoTag(1n, U.values(c, binding, public, PSource.phase_items(world, selected, input, phases))):
  match phases:
    case Nil{}: Unit{}
    case Con{+phase, rest}:
      L.Both{first({Nat.is_eq(U.tag(U.view(V.fact(c, binding, public, phase))), 1n) == False{} : Bool},
        {Nat.is_eq(U.tag(U.view(V.fact(c, binding, public, phase))), 4n) == False{} : Bool}, phase_other_kinds(c, binding, public, phase)),
        no_selection_phases(c, binding, public, world, selected, input, rest)}

def no_publication_phases(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +selected: D.State, +input: X.Reception, phases: List<&2, V.PreparationEvent>) ->
  U.NoTag(4n, U.values(c, binding, public, PSource.phase_items(world, selected, input, phases))):
  match phases:
    case Nil{}: Unit{}
    case Con{+phase, rest}:
      L.Both{second({Nat.is_eq(U.tag(U.view(V.fact(c, binding, public, phase))), 1n) == False{} : Bool},
        {Nat.is_eq(U.tag(U.view(V.fact(c, binding, public, phase))), 4n) == False{} : Bool}, phase_other_kinds(c, binding, public, phase)),
        no_publication_phases(c, binding, public, world, selected, input, rest)}

def plain_phases(+world: Nat, +selected: D.State, +input: X.Reception, phases: List<&2, V.PreparationEvent>) ->
  U.AllPlain(PSource.phase_items(world, selected, input, phases)):
  match phases:
    case Nil{}: Unit{}
    case Con{phase, rest}: L.Both{Unit{}, plain_phases(world, selected, input, rest)}

def source_all_plain(+world: Nat, +input: X.Reception, +before: E.Snapshot, run: V.PreparationRun) ->
  U.AllPlain(PSource.with_run(world, input, before, run)):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: L.Both{Unit{}, plain_phases(world, E.database(before), input, events)}

def source_selection_tag(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +before: E.Snapshot, run: V.PreparationRun) ->
  U.OnlyTag(1n, U.values(c, binding, public, PSource.with_run(world, input, before, run)), 0n, U.SelectedView{before}):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}:
      L.Both{{==}, L.Both{{==}, no_selection_phases(c, binding, public, world, E.database(before), input, events)}}

def source_no_publication(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +before: E.Snapshot, run: V.PreparationRun) ->
  U.NoTag(4n, U.values(c, binding, public, PSource.with_run(world, input, before, run))):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}:
      L.Both{{==}, no_publication_phases(c, binding, public, world, E.database(before), input, events)}

def selected_snapshot(value: U.View) -> Maybe<&2, E.Snapshot>:
  match value:
    case U.SelectedView{snapshot}: Some{snapshot}
    case _: None{}

def selection_result(-at: Nat, -other: E.Snapshot, -before: E.Snapshot,
  result: L.E<{at == 3n : Nat}, {U.SelectedView{other} == U.SelectedView{before} : U.View}>) ->
  L.E<{at == 3n : Nat}, {other == before : E.Snapshot}>:
  match result:
    case L.Both{time, snapshot}:
      L.Both{time, Equations.some_equality_is_injective_for_erased_indices(E.Snapshot, other, before,
        Equal.cong(U.View, Maybe<&2, E.Snapshot>, selected_snapshot, U.SelectedView{other}, U.SelectedView{before}, snapshot))}

law actual_preparation_source_derives_selection_uniqueness_for_all_returns:
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
  for ~returns: V.Returns
  E.SelectionUnique(O.environment(binding, public, c, seed, pi, artifacts,
    PSource.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw, returns), instance), Source.artifact(binding),
    I.Serve{world, c, seed(Unit{}), input}, 3n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})
def actual_preparation_source_derives_selection_uniqueness_for_all_returns(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, returns):
  at => other => observed =>
    selection_result(at, other, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}},
      U.actual_observation_inherits_only_the_derived_source_uniqueness(binding, public, c, seed, pi, artifacts,
        PSource.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw, returns), instance, 1n, 0n,
        U.SelectedView{E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}}, I.Serve{world, c, seed(Unit{}), input}, at, E.Selected{other}, U.SelectedView{other},
        source_all_plain(world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, V.run(c, mode, raw, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, returns)),
        source_selection_tag(c, binding, public, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, V.run(c, mode, raw, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, returns)),
        Unit{}, {==}, {==}, observed))

law actual_preparation_source_has_no_database_publication_for_any_return:
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
  for ~returns: V.Returns
  K.NonePublication(E.core_environment(True{}, O.environment(binding, public, c, seed, pi, artifacts,
    PSource.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw, returns), instance)), Source.artifact(binding),
    I.Serve{world, c, seed(Unit{}), input})
def actual_preparation_source_has_no_database_publication_for_any_return(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, returns):
  at => state => observed =>
    U.actual_observation_cannot_invent_a_tag_absent_from_its_source(binding, public, c, seed, pi, artifacts,
      PSource.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw, returns), instance, 4n,
      I.Serve{world, c, seed(Unit{}), input}, at, E.PreparedKernel{I.Published{state}}, U.PublicationView{state},
      source_all_plain(world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, V.run(c, mode, raw, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, returns)),
      source_no_publication(c, binding, public, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, V.run(c, mode, raw, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, returns)),
      Unit{}, {==}, {==}, observed)

def mutation_tag_success(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +before: E.Snapshot, +mode: V.Mode, +raw: P.Request,
  +context: D.Context, +entry: G.Entry, +bytes: List<&2, U32>, send: V.SendReturn) ->
  U.OnlyTag(2n, U.values(c, binding, public, PSource.with_run(world, input, before, A.success(mode, raw, context, before, entry, bytes, send))), 7n, U.MutationView{True{}, E.Register{entry}, before, V.registered_snapshot(before, A.registered(before, entry))}):
  match send:
    case V.SendPending{}:
      L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, Unit{}}}}}}}}}}}
    case V.SendComplete{}:
      L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, Unit{}}}}}}}}}}}}
    case V.SendInterrupted{prefix}:
      L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, Unit{}}}}}}}}}}}}}

def conclusion_tag_success(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +before: E.Snapshot, +mode: V.Mode, +raw: P.Request,
  +context: D.Context, +entry: G.Entry, +bytes: List<&2, U32>, send: V.SendReturn) ->
  U.OnlyTag(3n, U.values(c, binding, public, PSource.with_run(world, input, before, A.success(mode, raw, context, before, entry, bytes, send))), 8n, U.ConclusionView{E.Receipt{W.PreparedReceipt{G.handle(entry)}}, E.database(before), False{}}):
  match send:
    case V.SendPending{}:
      L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, Unit{}}}}}}}}}}}
    case V.SendComplete{}:
      L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, Unit{}}}}}}}}}}}}
    case V.SendInterrupted{prefix}:
      L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{{==}, Unit{}}}}}}}}}}}}}

def actual_mutation_tag(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +before: E.Snapshot, +mode: V.Mode, +raw: P.Request,
  +context: D.Context, +handle: String, +seal: String, +bytes: List<&2, U32>, +send: V.SendReturn,
  authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  fresh: {G.lookup(E.instance(before), handle, E.registry(before)) == None{} : Maybe<&2, G.Entry>},
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool},
  frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>}) ->
  U.OnlyTag(2n, U.values(c, binding, public, PSource.source(c, world, input, before, mode, raw,
    V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})), 7n, U.MutationView{True{}, E.Register{V.entry(mode, raw, E.instance(before), handle, seal)}, before, V.registered_snapshot(before, A.registered(before, V.entry(mode, raw, E.instance(before), handle, seal)))}):
  %Equal.sym(V.PreparationRun,
    V.run(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}),
    A.success(mode, raw, context, before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send),
    A.successful_preparation_has_the_exact_dispatcher_phases(c, mode, raw, before, context, handle, seal, bytes, send, authenticated, fresh, fits, frame)) :
      U.OnlyTag(2n, U.values(c, binding, public, PSource.with_run(world, input, before, _)), 7n, U.MutationView{True{}, E.Register{V.entry(mode, raw, E.instance(before), handle, seal)}, before, V.registered_snapshot(before, A.registered(before, V.entry(mode, raw, E.instance(before), handle, seal)))})
  mutation_tag_success(c, binding, public, world, input, before, mode, raw, context, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send)

def actual_conclusion_tag(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +before: E.Snapshot, +mode: V.Mode, +raw: P.Request,
  +context: D.Context, +handle: String, +seal: String, +bytes: List<&2, U32>, +send: V.SendReturn,
  authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  fresh: {G.lookup(E.instance(before), handle, E.registry(before)) == None{} : Maybe<&2, G.Entry>},
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool},
  frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>}) ->
  U.OnlyTag(3n, U.values(c, binding, public, PSource.source(c, world, input, before, mode, raw,
    V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})), 8n, U.ConclusionView{E.Receipt{W.PreparedReceipt{handle}}, E.database(before), False{}}):
  %Equal.sym(V.PreparationRun,
    V.run(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}),
    A.success(mode, raw, context, before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send),
    A.successful_preparation_has_the_exact_dispatcher_phases(c, mode, raw, before, context, handle, seal, bytes, send, authenticated, fresh, fits, frame)) :
      U.OnlyTag(3n, U.values(c, binding, public, PSource.with_run(world, input, before, _)), 8n, U.ConclusionView{E.Receipt{W.PreparedReceipt{handle}}, E.database(before), False{}})
  conclusion_tag_success(c, binding, public, world, input, before, mode, raw, context, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send)

def MutationMatches(-mode: Bool, -update: E.Mutation, -before: E.Snapshot, -after: E.Snapshot, actual: U.View) -> Type:
  match actual:
    case U.MutationView{other_mode, other_update, other_before, other_after}:
      L.E<{other_mode == mode : Bool}, L.E<{other_update == update : E.Mutation},
        L.E<{other_before == before : E.Snapshot}, {other_after == after : E.Snapshot}>>>
    case _: Unit

def mutation_payload(-mode: Bool, -update: E.Mutation, -before: E.Snapshot, -after: E.Snapshot,
  -other_mode: Bool, -other_update: E.Mutation, -other_before: E.Snapshot, -other_after: E.Snapshot,
  same: {U.MutationView{other_mode, other_update, other_before, other_after} == U.MutationView{mode, update, before, after} : U.View}) ->
  L.E<{other_mode == mode : Bool}, L.E<{other_update == update : E.Mutation},
    L.E<{other_before == before : E.Snapshot}, {other_after == after : E.Snapshot}>>>:
  %Equal.sym(U.View, U.MutationView{other_mode, other_update, other_before, other_after}, U.MutationView{mode, update, before, after}, same) :
    MutationMatches(mode, update, before, after, _)
  L.Both{{==}, L.Both{{==}, L.Both{{==}, {==}}}}

def mutation_result(-at: Nat, -mode: Bool, -update: E.Mutation, -before: E.Snapshot, -after: E.Snapshot,
  -other_mode: Bool, -other_update: E.Mutation, -other_before: E.Snapshot, -other_after: E.Snapshot,
  result: L.E<{at == 10n : Nat}, {U.MutationView{other_mode, other_update, other_before, other_after} == U.MutationView{mode, update, before, after} : U.View}>) ->
  L.E<{at == 10n : Nat}, L.E<{other_mode == mode : Bool}, L.E<{other_update == update : E.Mutation},
    L.E<{other_before == before : E.Snapshot}, {other_after == after : E.Snapshot}>>>>:
  match result:
    case L.Both{time, payload}: L.Both{time, mutation_payload(mode, update, before, after, other_mode, other_update, other_before, other_after, payload)}

law actual_successful_preparation_derives_full_mutation_uniqueness:
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
  for ~context: D.Context
  for ~handle: String
  for ~seal: String
  for ~bytes: List<&2, U32>
  for ~send: V.SendReturn
  for authenticated: {D.authenticate(seed(Unit{}), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}
  for fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool}
  for frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  E.MutationUnique(O.environment(binding, public, c, seed, pi, artifacts,
    PSource.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}), instance), Source.artifact(binding),
    I.Serve{world, c, seed(Unit{}), input}, 10n, True{}, E.Register{V.entry(mode, raw, instance, handle, seal)},
    E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}},
    V.registered_snapshot(E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, A.registered(E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, V.entry(mode, raw, instance, handle, seal))))
def actual_successful_preparation_derives_full_mutation_uniqueness(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, context, handle, seal, bytes, send, authenticated, fits, frame):
  at => other_mode => other_update => other_before => other_after => observed =>
    mutation_result(at, True{}, E.Register{V.entry(mode, raw, instance, handle, seal)}, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}},
      V.registered_snapshot(E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, A.registered(E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, V.entry(mode, raw, instance, handle, seal))),
      other_mode, other_update, other_before, other_after,
      U.actual_observation_inherits_only_the_derived_source_uniqueness(binding, public, c, seed, pi, artifacts,
        PSource.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
          V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}), instance, 2n, 7n,
        U.MutationView{True{}, E.Register{V.entry(mode, raw, instance, handle, seal)}, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}},
          V.registered_snapshot(E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, A.registered(E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, V.entry(mode, raw, instance, handle, seal)))},
        I.Serve{world, c, seed(Unit{}), input}, at, E.Mutated{other_mode, other_update, other_before, other_after}, U.MutationView{other_mode, other_update, other_before, other_after},
        source_all_plain(world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, V.run(c, mode, raw, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}},
          V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})),
        actual_mutation_tag(c, binding, public, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw, context, handle, seal, bytes, send, authenticated, {==}, fits, frame),
        Unit{}, {==}, {==}, observed))
