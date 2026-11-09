# Response causes and canonical bounded framing for deterministic cached-call
# rejections. No error cause or response-validity postcondition is a premise.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/PreparedLaws.bend as H
import ../contract/PreparedProtocol.bend as W
import ../contract/Requirements.bend as R
import ../contract/Resources.bend as X
import ../contract/Semantics.bend as S
import ../contract/Protocol.bend as P
import ./PreparedControlDispatch.bend as C
import ./HostTransitions.bend as Host
import ./PreparedDispatch.bend as E

def error_result(status: S.Status, +before: Host.Published) -> H.ControlResult:
  H.ControlResult{Host.database(before), Host.entries(before), H.Error{status}}

def CorrectReturn(~c: S.Configuration, -a: I.Environment, -artifacts: H.Artifacts,
  -native: String, -world: Nat, -time: Nat, +instance: String,
  +before: Host.Published, -input: X.Reception, -raw: P.Request, choice: E.Choice) -> Type:
  match choice:
    case E.Unauthenticated{}: C.ResultCorrect(error_result(S.Authentication{}, before), W.Execute{}, a, artifacts, native, world, time,
      c, Host.database(before), input, instance, Host.entries(before), raw)
    case E.BadProof{context}: C.ResultCorrect(error_result(S.Input{}, before), W.Execute{}, a, artifacts, native, world, time,
      c, Host.database(before), input, instance, Host.entries(before), raw)
    case E.Missing{context}: C.ResultCorrect(error_result(S.Failure{}, before), W.Execute{}, a, artifacts, native, world, time,
      c, Host.database(before), input, instance, Host.entries(before), raw)
    case E.Selected{context, entry}: Unit

def correct_error_returns(~c: S.Configuration, -a: I.Environment, -artifacts: H.Artifacts,
  -native: String, -world: Nat, -time: Nat, +instance: String,
  +before: Host.Published, -input: X.Reception, +raw: P.Request, choice: E.Choice,
  valid: {R.configuration_is_valid(c) == True{} : Bool},
  selected: E.Correct(c, instance, before, input, raw, choice)) ->
  CorrectReturn(c, a, artifacts, native, world, time, instance, before, input, raw, choice):
  match choice:
    case E.Unauthenticated{}:
      C.fixed_result_correct(c, S.Authentication{}, W.Execute{}, a, artifacts, native, world, time,
        Host.database(before), input, instance, Host.entries(before), raw, valid, Unit{}, L.Both{selected, {==}})
    case E.BadProof{context}:
      match selected:
        case L.Both{authenticated, nonempty}:
          C.fixed_result_correct(c, S.Input{}, W.Execute{}, a, artifacts, native, world, time,
            Host.database(before), input, instance, Host.entries(before), raw, valid, Unit{},
            (context, L.Both{Unit{}, L.Both{authenticated, L.Both{nonempty, {==}}}}))
    case E.Missing{context}:
      match selected:
        case L.Both{authenticated, L.Both{empty, absent}}:
          C.fixed_result_correct(c, S.Failure{}, W.Execute{}, a, artifacts, native, world, time,
            Host.database(before), input, instance, Host.entries(before), raw, valid, Unit{},
            L.Left{(context, L.Both{Unit{}, L.Both{authenticated, L.Both{empty, L.Both{absent, {==}}}}})})
    case E.Selected{context, entry}: Unit{}

def Returned(~c: S.Configuration, -a: I.Environment, -artifacts: H.Artifacts,
  -native: String, -world: Nat, -time: Nat, +instance: String,
  +before: Host.Published, -input: X.Reception, -raw: P.Request, choice: E.Choice) -> Type:
  match choice:
    case E.Unauthenticated{}:
      &bytes: List<&2, U32> -> H.ControlOutcome(a, artifacts, native, world, c, Host.database(before),
        input, time, instance, Host.entries(before), W.Execute{}, raw, error_result(S.Authentication{}, before),
        Host.response(before), Host.response(before), bytes)
    case E.BadProof{context}:
      &bytes: List<&2, U32> -> H.ControlOutcome(a, artifacts, native, world, c, Host.database(before),
        input, time, instance, Host.entries(before), W.Execute{}, raw, error_result(S.Input{}, before),
        Host.response(before), Host.response(before), bytes)
    case E.Missing{context}:
      &bytes: List<&2, U32> -> H.ControlOutcome(a, artifacts, native, world, c, Host.database(before),
        input, time, instance, Host.entries(before), W.Execute{}, raw, error_result(S.Failure{}, before),
        Host.response(before), Host.response(before), bytes)
    case E.Selected{context, entry}: Unit

def framed_returns(~c: S.Configuration, -a: I.Environment, -artifacts: H.Artifacts,
  -native: String, -world: Nat, -time: Nat, +instance: String,
  +before: Host.Published, -input: X.Reception, -raw: P.Request, choice: E.Choice,
  valid: {R.configuration_is_valid(c) == True{} : Bool},
  received: W.Received(c, input, W.Extension{W.Execute{}, raw}),
  correct: CorrectReturn(c, a, artifacts, native, world, time, instance, before, input, raw, choice)) ->
  Returned(c, a, artifacts, native, world, time, instance, before, input, raw, choice):
  match choice:
    case E.Unauthenticated{}:
      C.correct_result_has_control_outcome(c, W.Execute{}, a, artifacts, native, world, time,
        Host.database(before), input, instance, Host.entries(before), raw, error_result(S.Authentication{}, before),
        Host.response(before), valid, received, correct)
    case E.BadProof{context}:
      C.correct_result_has_control_outcome(c, W.Execute{}, a, artifacts, native, world, time,
        Host.database(before), input, instance, Host.entries(before), raw, error_result(S.Input{}, before),
        Host.response(before), valid, received, correct)
    case E.Missing{context}:
      C.correct_result_has_control_outcome(c, W.Execute{}, a, artifacts, native, world, time,
        Host.database(before), input, instance, Host.entries(before), raw, error_result(S.Failure{}, before),
        Host.response(before), valid, received, correct)
    case E.Selected{context, entry}: Unit{}

def returns_with_physical_pair(~c: S.Configuration, -a: I.Environment, -artifacts: H.Artifacts,
  -native: String, -world: Nat, -time: Nat, +instance: String,
  +before: Host.Published, +input: X.Reception, +raw: P.Request,
  +valid: {R.configuration_is_valid(c) == True{} : Bool},
  received: L.E<W.Received(c, input, W.Extension{W.Execute{}, raw}), W.Received(c, input, W.Extension{W.Execute{}, raw})>) ->
  Returned(c, a, artifacts, native, world, time, instance, before, input, raw, E.choose(instance, before, raw)):
  match received:
    case L.Both{selection, response}:
      framed_returns(c, a, artifacts, native, world, time, instance, before, input, raw,
        E.choose(instance, before, raw), valid, response,
        correct_error_returns(c, a, artifacts, native, world, time, instance, before, input, raw,
          E.choose(instance, before, raw), valid,
          E.deterministic_cached_selection_has_only_exact_error_causes_or_current_authenticated_entry(c, instance, before, input, raw, selection)))

law deterministic_cached_rejections_have_exact_cause_and_complete_bounded_physical_response:
  for ~c: S.Configuration
  for -a: I.Environment
  for -artifacts: H.Artifacts
  for -native: String
  for -world: Nat
  for -time: Nat
  for +instance: String
  for +before: Host.Published
  for +input: X.Reception
  for +raw: P.Request
  for valid: {R.configuration_is_valid(c) == True{} : Bool}
  for received: W.Received(c, input, W.Extension{W.Execute{}, raw})
  Returned(c, a, artifacts, native, world, time, instance, before, input, raw, E.choose(instance, before, raw))
def deterministic_cached_rejections_have_exact_cause_and_complete_bounded_physical_response(c, a, artifacts, native, world, time,
  instance, before, input, raw, valid, received):
  returns_with_physical_pair(c, a, artifacts, native, world, time, instance, before, input, raw, valid,
    C.physical_reception_data_can_be_reused(c, input, W.Extension{W.Execute{}, raw}, received))
