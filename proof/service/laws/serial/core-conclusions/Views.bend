# Translate independent occurrence data to the unchanged service-view tags.
# These are local proof adapters; actual source generation supplies every fact.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/Semantics.bend as S
import ../../../../../contract/Resources.bend as X
import ../../../specification/ServiceLaws.bend as E
import ../../../../Foundations.bend as F
import ../../../../SourceService.bend as Source
import ../../../model/EventObserver.bend as O
import ../../../model/ObservationUniqueness.bend as U
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Common.bend as C
import ../../../model/serial/Engine.bend as Engine
import ./Meaning.bend as M
import ./Projection.bend as P

def absent_none(value: Maybe<&2, M.Endpoint>, absent: {M.absent(value) == True{} : Bool}) -> {value == None{} : Maybe<&2, M.Endpoint>}:
  match value:
    case None{}: {==}
    case Some{endpoint}: L.ex_false({Some{endpoint} == None{} : Maybe<&2, M.Endpoint>}, F.false_negative_true(absent))

def normalized_none(+view: U.View, none: {P.normalized(view) == None{} : Maybe<&2, U.View>}) -> {Nat.is_eq(U.tag(view), 3n) == False{} : Bool}:
  match view:
    case U.VoidView{}: {==}
    case U.SelectedView{snapshot}: {==}
    case U.MutationView{mode, mutation, before, after}: {==}
    case U.PublicationView{state}: {==}
    case U.ConclusionView{outcome, state, closes}:
      L.ex_false({Nat.is_eq(3n, 3n) == False{} : Bool}, F.none_negative_some(U.View, U.ConclusionView{outcome, state, closes}, Equal.sym(Maybe<&2, U.View>, Some{U.ConclusionView{outcome, state, closes}}, None{}, none)))

def normalized_some(+view: U.View, +expected: U.View, found: {P.normalized(view) == Some{expected} : Maybe<&2, U.View>}) -> {view == expected : U.View}:
  match view:
    case U.VoidView{}: L.ex_false({U.VoidView{} == expected : U.View}, F.none_negative_some(U.View, expected, found))
    case U.SelectedView{snapshot}: L.ex_false({U.SelectedView{snapshot} == expected : U.View}, F.none_negative_some(U.View, expected, found))
    case U.MutationView{mode, mutation, before, after}: L.ex_false({U.MutationView{mode, mutation, before, after} == expected : U.View}, F.none_negative_some(U.View, expected, found))
    case U.PublicationView{state}: L.ex_false({U.PublicationView{state} == expected : U.View}, F.none_negative_some(U.View, expected, found))
    case U.ConclusionView{outcome, state, closes}: F.some_injective(U.View, U.ConclusionView{outcome, state, closes}, expected, found)

def quiet_event(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +event: O.AuditEvent,
  absent: {M.absent(M.endpoint(event)) == True{} : Bool}) ->
  {Nat.is_eq(U.tag(U.view(O.fact(c, binding, public, event))), 3n) == False{} : Bool}:
  normalized_none(U.view(O.fact(c, binding, public, event)),
    Equal.trans(Maybe<&2, U.View>, P.normalized(U.view(O.fact(c, binding, public, event))), P.endpoint_view(M.endpoint(event)), None{}, P.event_endpoint(c, binding, public, event),
      Equal.cong(Maybe<&2, M.Endpoint>, Maybe<&2, U.View>, P.endpoint_view, M.endpoint(event), None{}, absent_none(M.endpoint(event), absent))))

def quiet(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +selected: D.State, events: List<&2, O.AuditEvent>, +none: {M.quiet(events) == True{} : Bool}) ->
  U.NoTag(3n, U.values(c, binding, public, Engine.stamp(world, input, selected, events))):
  match events:
    case Nil{}: Unit{}
    case Con{+head, +tail}:
      L.Both{quiet_event(c, binding, public, head, F.and_boolean_left(M.absent(M.endpoint(head)), M.quiet(tail), none)),
        quiet(c, binding, public, world, input, selected, tail, F.and_boolean_right(M.absent(M.endpoint(head)), M.quiet(tail), none))}

def transaction(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +event: O.AuditEvent,
  +response: S.Response, +state: D.State, +closes: Bool, actual: {M.endpoint(event) == Some{M.Transaction{response, state, closes}} : Maybe<&2, M.Endpoint>}) ->
  {U.view(O.fact(c, binding, public, event)) == U.ConclusionView{E.Transaction{response}, state, closes} : U.View}:
  normalized_some(U.view(O.fact(c, binding, public, event)), U.ConclusionView{E.Transaction{response}, state, closes},
    Equal.trans(Maybe<&2, U.View>, P.normalized(U.view(O.fact(c, binding, public, event))), P.endpoint_view(M.endpoint(event)), Some{U.ConclusionView{E.Transaction{response}, state, closes}}, P.event_endpoint(c, binding, public, event),
      Equal.cong(Maybe<&2, M.Endpoint>, Maybe<&2, U.View>, P.endpoint_view, M.endpoint(event), Some{M.Transaction{response, state, closes}}, actual)))

def unique_after(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +selected: D.State, prefix: List<&2, O.AuditEvent>, +event: O.AuditEvent, +suffix: List<&2, O.AuditEvent>, +expected: U.View,
  +same: {U.view(O.fact(c, binding, public, event)) == expected : U.View}, +tagged: {U.tag(expected) == 3n : Nat},
  left: U.NoTag(3n, U.values(c, binding, public, Engine.stamp(world, input, selected, prefix))),
  right: U.NoTag(3n, U.values(c, binding, public, Engine.stamp(world, input, selected, suffix)))) ->
  U.OnlyTag(3n, U.values(c, binding, public, Engine.stamp(world, input, selected, C.append(prefix, Con{event, suffix}))), B.count(O.AuditEvent, prefix), expected):
  match prefix left:
    case Nil{} unit: L.Both{same, L.Both{Equal.trans(Nat, U.tag(U.view(O.fact(c, binding, public, event))), U.tag(expected), 3n,
      Equal.cong(U.View, Nat, U.tag, U.view(O.fact(c, binding, public, event)), expected, same), tagged), right}}
    case Con{head, rest} L.Both{first, remaining}:
      L.Both{first, unique_after(c, binding, public, world, input, selected, rest, event, suffix, expected, same, tagged, remaining, right)}

def metadata(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +event: O.AuditEvent,
  +receipt: W.Receipt, +result: H.ControlResult, +snapshot: E.Snapshot, +closes: Bool,
  actual: {M.endpoint(event) == Some{M.Metadata{receipt, result, snapshot, closes}} : Maybe<&2, M.Endpoint>}) ->
  {U.view(O.fact(c, binding, public, event)) == U.ConclusionView{E.Receipt{receipt}, E.database(snapshot), closes} : U.View}:
  normalized_some(U.view(O.fact(c, binding, public, event)), U.ConclusionView{E.Receipt{receipt}, E.database(snapshot), closes},
    Equal.trans(Maybe<&2, U.View>, P.normalized(U.view(O.fact(c, binding, public, event))), P.endpoint_view(M.endpoint(event)), Some{U.ConclusionView{E.Receipt{receipt}, E.database(snapshot), closes}}, P.event_endpoint(c, binding, public, event),
      Equal.cong(Maybe<&2, M.Endpoint>, Maybe<&2, U.View>, P.endpoint_view, M.endpoint(event), Some{M.Metadata{receipt, result, snapshot, closes}}, actual)))
