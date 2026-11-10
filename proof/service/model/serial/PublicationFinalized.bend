# Real preparation/conclusion equations derive the exact final working state
# and finalized response. No certification of a runtime result is an input.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Logic.bend as L
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Requirements.bend as R
import ../../../../contract/Semantics.bend as S
import ../../../../src/Core.bend as Core
import ../../../ConclusionService.bend as Conclusion
import ../../../Foundations.bend as F
import ../../../Preparation.bend as Preparation
import ../../../ProtocolService.bend as Q
import ../../specification/ServiceLaws.bend as E
import ../EventObserver.bend as O
import ./PublicationAuthority.bend as Authority
import ./PublicationConclusions.bend as Conclusions


def Finalized(~c: S.Configuration, -trace: S.Trace, -response: S.Response, +state: D.State) -> Type:
  &events: List<&2, S.OperationEvent> -> &proposal: S.Response ->
    L.E<{trace == S.Final{state, events, proposal} : S.Trace}, {R.finalize(proposal, c, state) == response : S.Response}>


def response(conclusion: Core.Conclusion) -> S.Response:
  Core.Conclusion{state, response, bytes} = conclusion
  response


def state(conclusion: Core.Conclusion) -> D.State:
  Core.Conclusion{state, response, bytes} = conclusion
  state


def publish_success(+response: S.Response, -initial: D.State, -working: D.State, success: {Authority.response_status(response) == S.Success{} : S.Status}) -> {S.publish(response, initial, working) == working : D.State}:
  match response:
    case S.Response{S.Success{}, value}: {==}
    case S.Response{S.Refusal{}, value}: L.ex_false({initial == working : D.State}, F.false_negative_true(Equal.cong(S.Status, Bool, S.is_success, S.Refusal{}, S.Success{}, success)))
    case S.Response{S.Input{}, value}: L.ex_false({initial == working : D.State}, F.false_negative_true(Equal.cong(S.Status, Bool, S.is_success, S.Input{}, S.Success{}, success)))
    case S.Response{S.Authentication{}, value}: L.ex_false({initial == working : D.State}, F.false_negative_true(Equal.cong(S.Status, Bool, S.is_success, S.Authentication{}, S.Success{}, success)))
    case S.Response{S.Certificate{}, value}: L.ex_false({initial == working : D.State}, F.false_negative_true(Equal.cong(S.Status, Bool, S.is_success, S.Certificate{}, S.Success{}, success)))
    case S.Response{S.DataError{}, value}: L.ex_false({initial == working : D.State}, F.false_negative_true(Equal.cong(S.Status, Bool, S.is_success, S.DataError{}, S.Success{}, success)))
    case S.Response{S.Limit{}, value}: L.ex_false({initial == working : D.State}, F.false_negative_true(Equal.cong(S.Status, Bool, S.is_success, S.Limit{}, S.Success{}, success)))
    case S.Response{S.Failure{}, value}: L.ex_false({initial == working : D.State}, F.false_negative_true(Equal.cong(S.Status, Bool, S.is_success, S.Failure{}, S.Success{}, success)))


def result(~c: S.Configuration, +working: D.State, +events: List<&2, S.OperationEvent>, +proposal: S.Response, +actual_response: S.Response, +published: D.State,
  states: L.E<{published == working : D.State}, {published == working : D.State}>, finalized: {actual_response == R.finalize(proposal, c, working) : S.Response}) -> Finalized(c, S.Final{working, events, proposal}, actual_response, published):
  match states:
    case L.Both{at_trace, at_response}:
      (events, proposal, L.Both{Equal.cong(D.State, S.Trace, value => S.Final{value, events, proposal}, working, published, Equal.sym(D.State, published, working, at_trace)),
        (%Equal.sym(D.State, published, working, at_response) : {R.finalize(proposal, c, _) == actual_response : S.Response}
          Equal.sym(S.Response, actual_response, R.finalize(proposal, c, working), finalized))})


def states_from_fields(~c: S.Configuration, +initial: D.State, +working: D.State, +proposal: S.Response, +actual_response: S.Response, +published: D.State,
  finalized: {actual_response == R.finalize(proposal, c, working) : S.Response},
  actual: {published == S.publish(R.finalize(proposal, c, working), initial, working) : D.State}, success: {Authority.response_status(actual_response) == S.Success{} : S.Status}) -> {published == working : D.State}:
  Equal.trans(D.State, published, S.publish(R.finalize(proposal, c, working), initial, working), working, actual,
    Equal.trans(D.State, S.publish(R.finalize(proposal, c, working), initial, working), S.publish(actual_response, initial, working), working,
      Equal.cong(S.Response, D.State, value => S.publish(value, initial, working), R.finalize(proposal, c, working), actual_response, Equal.sym(S.Response, actual_response, R.finalize(proposal, c, working), finalized)), publish_success(actual_response, initial, working, success)))


def canonical_response(~c: S.Configuration, +before: E.Snapshot, +working: D.State, +events: List<&2, S.OperationEvent>, +proposal: S.Response, -prepared_bytes: List<&2, U32>,
  +actual_response: S.Response, -bytes: List<&2, U32>, +after: E.Snapshot,
  responses: L.E<{actual_response == R.finalize(proposal, c, working) : S.Response}, {actual_response == R.finalize(proposal, c, working) : S.Response}>,
  actual: {E.database(after) == S.publish(R.finalize(proposal, c, working), E.database(before), working) : D.State}, success: {Authority.response_status(actual_response) == S.Success{} : S.Status}) -> Finalized(c, S.Final{working, events, proposal}, actual_response, E.database(after)):
  match responses:
    case L.Both{at_state, retained}:
      result(c, working, events, proposal, actual_response, E.database(after),
        Q.equality_reopenable(D.State, E.database(after), working, states_from_fields(c, E.database(before), working, proposal, actual_response, E.database(after), at_state, actual, success)), retained)


def canonical(~c: S.Configuration, +before: E.Snapshot, +working: D.State, +events: List<&2, S.OperationEvent>, +proposal: S.Response, +prepared_bytes: List<&2, U32>,
  +actual_response: S.Response, +bytes: List<&2, U32>, +after: E.Snapshot,
  conclusions: L.E<{Core.Conclusion{E.database(after), actual_response, bytes} == Core.conclude(Core.Prepared{working, events, R.finalize(proposal, c, working), prepared_bytes}, E.database(before)) : Core.Conclusion},
    {Core.Conclusion{E.database(after), actual_response, bytes} == Core.conclude(Core.Prepared{working, events, R.finalize(proposal, c, working), prepared_bytes}, E.database(before)) : Core.Conclusion}>,
  success: {Authority.response_status(actual_response) == S.Success{} : S.Status}) -> Finalized(c, S.Final{working, events, proposal}, actual_response, E.database(after)):
  match conclusions:
    case L.Both{at_response, at_state}:
      canonical_response(c, before, working, events, proposal, prepared_bytes, actual_response, bytes, after,
        Q.equality_reopenable(S.Response, actual_response, R.finalize(proposal, c, working), Equal.cong(Core.Conclusion, S.Response, response,
          Core.Conclusion{E.database(after), actual_response, bytes}, Core.conclude(Core.Prepared{working, events, R.finalize(proposal, c, working), prepared_bytes}, E.database(before)), at_response)),
        Equal.cong(Core.Conclusion, D.State, state, Core.Conclusion{E.database(after), actual_response, bytes}, Core.conclude(Core.Prepared{working, events, R.finalize(proposal, c, working), prepared_bytes}, E.database(before)), at_state), success)


def canonical_actual(~c: S.Configuration, +mode: Bool, +before: E.Snapshot, +working: D.State, +events: List<&2, S.OperationEvent>, +proposal: S.Response, +prepared_bytes: List<&2, U32>,
  +actual_mode: Bool, +actual_response: S.Response, +bytes: List<&2, U32>, +actual_before: E.Snapshot, +after: E.Snapshot,
  actual: Conclusions.Actual(mode, before, Core.conclude(Core.Prepared{working, events, R.finalize(proposal, c, working), prepared_bytes}, E.database(before)), O.Publication{actual_mode, actual_response, bytes, actual_before, after})) ->
  Finalized(c, S.Final{working, events, proposal}, actual_response, E.database(after)):
  match actual:
    case L.Both{at_mode, L.Both{conclusion, L.Both{at_before, success}}}:
      canonical(c, before, working, events, proposal, prepared_bytes, actual_response, bytes, after,
        Q.equality_reopenable(Core.Conclusion, Core.Conclusion{E.database(after), actual_response, bytes}, Core.conclude(Core.Prepared{working, events, R.finalize(proposal, c, working), prepared_bytes}, E.database(before)), conclusion), success)


def normalized(~c: S.Configuration, +mode: Bool, +before: E.Snapshot, +working: D.State, +events: List<&2, S.OperationEvent>, +proposal: S.Response, +prepared: Core.Prepared,
  +actual_mode: Bool, +actual_response: S.Response, +bytes: List<&2, U32>, +actual_before: E.Snapshot, +after: E.Snapshot,
  normalization: {prepared == Core.Prepared{working, events, R.finalize(proposal, c, working), Preparation.bytes_prepared(prepared)} : Core.Prepared},
  actual: Conclusions.Actual(mode, before, Core.conclude(prepared, E.database(before)), O.Publication{actual_mode, actual_response, bytes, actual_before, after})) ->
  Finalized(c, S.Final{working, events, proposal}, actual_response, E.database(after)):
  canonical_actual(c, mode, before, working, events, proposal, Preparation.bytes_prepared(prepared), actual_mode, actual_response, bytes, actual_before, after,
    (%normalization : Conclusions.Actual(mode, before, Core.conclude(_, E.database(before)), O.Publication{actual_mode, actual_response, bytes, actual_before, after}) actual))


law actual_preparation_and_publication_derive_the_exact_finalized_working_state_and_response:
  for ~c: S.Configuration
  for +mode: Bool
  for +before: E.Snapshot
  for +working: D.State
  for +events: List<&2, S.OperationEvent>
  for +proposal: S.Response
  for +prepared: Core.Prepared
  for +actual_mode: Bool
  for +actual_response: S.Response
  for +bytes: List<&2, U32>
  for +actual_before: E.Snapshot
  for +after: E.Snapshot
  for obtained: {Core.prepare(Core.Stopped{working, events, proposal}, c) == Some{prepared} : Maybe<&2, Core.Prepared>}
  for actual: Conclusions.Actual(mode, before, Core.conclude(prepared, E.database(before)), O.Publication{actual_mode, actual_response, bytes, actual_before, after})
  Finalized(c, S.Final{working, events, proposal}, actual_response, E.database(after))
def actual_preparation_and_publication_derive_the_exact_finalized_working_state_and_response(c, mode, before, working, events, proposal, prepared, actual_mode, actual_response, bytes, actual_before, after, obtained, actual):
  normalized(c, mode, before, working, events, proposal, prepared, actual_mode, actual_response, bytes, actual_before, after,
    L.and_left({prepared == Core.Prepared{working, events, R.finalize(proposal, c, working), Preparation.bytes_prepared(prepared)} : Core.Prepared},
      P.Message(S.response_value(R.finalize(proposal, c, working)), Preparation.bytes_prepared(prepared)), Conclusion.normalize_prepared_real(c, working, events, proposal, prepared, obtained)), actual)
