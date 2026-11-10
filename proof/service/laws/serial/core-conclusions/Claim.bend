# A queried conclusion recovers its exact earlier prepared occurrence and
# actual unique source slot. This statement is independent of source branches.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Semantics.bend as S
import ../../../../Foundations.bend as F
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/ObservationUniqueness.bend as U
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Common.bend as C
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/AuditQueries.bend as Query
import ./Meaning.bend as M
import ./Views.bend as V

def Claim(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +selected: D.State, +events: List<&2, O.AuditEvent>, -index: Nat, +response: S.Response, +state: D.State, +closes: Bool) -> Type:
  L.E<{closes == False{} : Bool},
    &bytes: List<&2, U32> -> &prepared_at: Nat -> &prepared_event: O.AuditEvent ->
      L.E<{Nat.is_lt(prepared_at, index) == True{} : Bool},
        L.E<{B.query(O.AuditEvent, events, prepared_at) == Some{prepared_event} : Maybe<&2, O.AuditEvent>},
          L.E<{M.prepared(prepared_event) == Some{M.Framing{response, bytes}} : Maybe<&2, M.Framing>},
            U.OnlyTag(3n, U.values(c, binding, public, Engine.stamp(world, input, selected, events)), index, U.ConclusionView{E.Transaction{response}, state, closes})>>>>

def ForView(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +selected: D.State, +events: List<&2, O.AuditEvent>, -index: Nat, view: U.View) -> Type:
  match view:
    case U.ConclusionView{E.Transaction{response}, state, closes}: Claim(c, binding, public, world, input, selected, events, index, response, state, closes)
    case _: Empty

def lifted_prepared(+events: List<&2, O.AuditEvent>, +prefix: List<&2, O.AuditEvent>, +head: O.AuditEvent, +suffix: List<&2, O.AuditEvent>, +index: Nat, +prepared: O.AuditEvent,
  layout: {events == C.append(prefix, Con{head, suffix}) : List<&2, O.AuditEvent>},
  query: {B.query(O.AuditEvent, prefix, index) == Some{prepared} : Maybe<&2, O.AuditEvent>}) ->
  {B.query(O.AuditEvent, events, index) == Some{prepared} : Maybe<&2, O.AuditEvent>}:
  %Equal.sym(List<&2, O.AuditEvent>, events, C.append(prefix, Con{head, suffix}), layout) : {B.query(O.AuditEvent, _, index) == Some{prepared} : Maybe<&2, O.AuditEvent>}
  Query.prefix_query(prefix, Con{head, suffix}, index, prepared, query)

def unique(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +selected: D.State, +events: List<&2, O.AuditEvent>,
  +prefix: List<&2, O.AuditEvent>, +suffix: List<&2, O.AuditEvent>, +event: O.AuditEvent, +expected: U.View,
  layout: {events == C.append(prefix, Con{event, suffix}) : List<&2, O.AuditEvent>},
  same: {U.view(O.fact(c, binding, public, event)) == expected : U.View}, tag: {U.tag(expected) == 3n : Nat},
  left: {M.quiet(prefix) == True{} : Bool}, right: {M.quiet(suffix) == True{} : Bool}) ->
  U.OnlyTag(3n, U.values(c, binding, public, Engine.stamp(world, input, selected, events)), B.count(O.AuditEvent, prefix), expected):
  %Equal.sym(List<&2, O.AuditEvent>, events, C.append(prefix, Con{event, suffix}), layout) : U.OnlyTag(3n, U.values(c, binding, public, Engine.stamp(world, input, selected, _)), B.count(O.AuditEvent, prefix), expected)
  V.unique_after(c, binding, public, world, input, selected, prefix, event, suffix, expected, same, tag,
    V.quiet(c, binding, public, world, input, selected, prefix, left), V.quiet(c, binding, public, world, input, selected, suffix, right))

def known(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +selected: D.State, +events: List<&2, O.AuditEvent>,
  +prefix: List<&2, O.AuditEvent>, +suffix: List<&2, O.AuditEvent>, +event: O.AuditEvent, +response: S.Response, +state: D.State, +bytes: List<&2, U32>, +prepared_at: Nat, +prepared_event: O.AuditEvent,
  +layout: {events == C.append(prefix, Con{event, suffix}) : List<&2, O.AuditEvent>},
  concluded: {M.endpoint(event) == Some{M.Transaction{response, state, False{}}} : Maybe<&2, M.Endpoint>},
  left: {M.quiet(prefix) == True{} : Bool}, right: {M.quiet(suffix) == True{} : Bool},
  +query: {B.query(O.AuditEvent, prefix, prepared_at) == Some{prepared_event} : Maybe<&2, O.AuditEvent>}, payload: {M.prepared(prepared_event) == Some{M.Framing{response, bytes}} : Maybe<&2, M.Framing>}) ->
  Claim(c, binding, public, world, input, selected, events, B.count(O.AuditEvent, prefix), response, state, False{}):
  L.Both{{==}, (bytes, prepared_at, prepared_event,
    L.Both{B.successful_query_is_strictly_inside_actual_list(O.AuditEvent, prefix, prepared_at, prepared_event, query),
      L.Both{lifted_prepared(events, prefix, event, suffix, prepared_at, prepared_event, layout, query),
        L.Both{payload, unique(c, binding, public, world, input, selected, events, prefix, suffix, event, U.ConclusionView{E.Transaction{response}, state, False{}}, layout,
          V.transaction(c, binding, public, event, response, state, False{}, concluded), {==}, left, right)}}})}

def move(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +selected: D.State, +events: List<&2, O.AuditEvent>, -index: Nat, -expected_index: Nat, +view: U.View, +expected_view: U.View,
  located: L.E<{index == expected_index : Nat}, {view == expected_view : U.View}>,
  claim: ForView(c, binding, public, world, input, selected, events, expected_index, expected_view)) ->
  ForView(c, binding, public, world, input, selected, events, index, view):
  match located:
    case L.Both{same_index, same_view}:
      %Equal.sym(U.View, view, expected_view, same_view) : ForView(c, binding, public, world, input, selected, events, index, _)
      %Equal.sym(Nat, index, expected_index, same_index) : ForView(c, binding, public, world, input, selected, events, _, expected_view)
      claim

def is_transaction(view: U.View) -> Bool:
  match view:
    case U.ConclusionView{E.Transaction{response}, state, closes}: True{}
    case _: False{}

def reject_location(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +selected: D.State, +events: List<&2, O.AuditEvent>, -index: Nat, -expected_index: Nat,
  +response: S.Response, +state: D.State, +closes: Bool, +receipt: W.Receipt, +snapshot: E.Snapshot, +closing: Bool,
  located: L.E<{index == expected_index : Nat}, {U.ConclusionView{E.Transaction{response}, state, closes} == U.ConclusionView{E.Receipt{receipt}, E.database(snapshot), closing} : U.View}>) ->
  Claim(c, binding, public, world, input, selected, events, index, response, state, closes):
  match located:
    case L.Both{position, same}:
      L.ex_false(Claim(c, binding, public, world, input, selected, events, index, response, state, closes),
        F.false_negative_true(Equal.sym(Bool, True{}, False{}, Equal.cong(U.View, Bool, is_transaction,
          U.ConclusionView{E.Transaction{response}, state, closes}, U.ConclusionView{E.Receipt{receipt}, E.database(snapshot), closing}, same))))

def reject_metadata(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +selected: D.State, +events: List<&2, O.AuditEvent>, +index: Nat,
  +response: S.Response, +state: D.State, +closes: Bool, +expected_index: Nat, +receipt: W.Receipt, +snapshot: E.Snapshot, +closing: Bool,
  query: {B.query(U.View, U.values(c, binding, public, Engine.stamp(world, input, selected, events)), index) == Some{U.ConclusionView{E.Transaction{response}, state, closes}} : Maybe<&2, U.View>},
  unique: U.OnlyTag(3n, U.values(c, binding, public, Engine.stamp(world, input, selected, events)), expected_index, U.ConclusionView{E.Receipt{receipt}, E.database(snapshot), closing})) ->
  Claim(c, binding, public, world, input, selected, events, index, response, state, closes):
  reject_location(c, binding, public, world, input, selected, events, index, expected_index, response, state, closes, receipt, snapshot, closing,
    U.a_structurally_unique_source_tag_has_the_exact_index_and_payload(3n, U.values(c, binding, public, Engine.stamp(world, input, selected, events)), expected_index, index,
      U.ConclusionView{E.Receipt{receipt}, E.database(snapshot), closing}, U.ConclusionView{E.Transaction{response}, state, closes}, unique, query, {==}))

law any_queried_transaction_conclusion_recovers_its_exact_framing_and_unique_shared_source_slot:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +world: Nat
  for +input: X.Reception
  for +selected: D.State
  for +events: List<&2, O.AuditEvent>
  for +index: Nat
  for +response: S.Response
  for +state: D.State
  for +closes: Bool
  for query: {B.query(U.View, U.values(c, binding, public, Engine.stamp(world, input, selected, events)), index) == Some{U.ConclusionView{E.Transaction{response}, state, closes}} : Maybe<&2, U.View>}
  for shape: M.Shape<events>
  Claim(c, binding, public, world, input, selected, events, index, response, state, closes)
def any_queried_transaction_conclusion_recovers_its_exact_framing_and_unique_shared_source_slot(c, binding, public, world, input, selected, events, index, response, state, closes, query, shape):
  match shape:
    case M.Quiet{none}:
      L.ex_false(Claim(c, binding, public, world, input, selected, events, index, response, state, closes),
        U.an_excluded_source_tag_cannot_be_queried(3n, U.values(c, binding, public, Engine.stamp(world, input, selected, events)), index, U.ConclusionView{E.Transaction{response}, state, closes},
          V.quiet(c, binding, public, world, input, selected, events, none), query, {==}))
    case M.TransactionShape{+prefix, +suffix, +event, +actual_response, +actual_state, +bytes, +prepared_at, +prepared_event, +layout, +concluded, +left, +right, +prepared_query, payload}:
      move(c, binding, public, world, input, selected, events, index, B.count(O.AuditEvent, prefix), U.ConclusionView{E.Transaction{response}, state, closes}, U.ConclusionView{E.Transaction{actual_response}, actual_state, False{}},
        U.a_structurally_unique_source_tag_has_the_exact_index_and_payload(3n, U.values(c, binding, public, Engine.stamp(world, input, selected, events)), B.count(O.AuditEvent, prefix), index, U.ConclusionView{E.Transaction{actual_response}, actual_state, False{}}, U.ConclusionView{E.Transaction{response}, state, closes},
          unique(c, binding, public, world, input, selected, events, prefix, suffix, event, U.ConclusionView{E.Transaction{actual_response}, actual_state, False{}}, layout, V.transaction(c, binding, public, event, actual_response, actual_state, False{}, concluded), {==}, left, right), query, {==}),
        known(c, binding, public, world, input, selected, events, prefix, suffix, event, actual_response, actual_state, bytes, prepared_at, prepared_event, layout, concluded, left, right, prepared_query, payload))
    case M.MetadataShape{+prefix, +suffix, +event, +receipt, +result, +snapshot, +closing, layout, concluded, left, right}:
      reject_metadata(c, binding, public, world, input, selected, events, index, response, state, closes, B.count(O.AuditEvent, prefix), receipt, snapshot, closing, query,
        unique(c, binding, public, world, input, selected, events, prefix, suffix, event, U.ConclusionView{E.Receipt{receipt}, E.database(snapshot), closing}, layout, V.metadata(c, binding, public, event, receipt, result, snapshot, closing, concluded), {==}, left, right))
