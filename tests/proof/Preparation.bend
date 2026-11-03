# Technical regression. Proposals violating T laws are not admitted;
# these cases exercise finalize/prepare directly, without simulating admission.
import Base
import ../../contract/Data.bend as D
import ../../contract/Semantics.bend as S
import ../../contract/Requirements.bend as R
import ../../src/Core.bend as N
import ../../proof/Publication.bend as U
import ./Certificate.bend as T

def empty() -> D.State:
  D.State{Nil{}, [T.user("a", ""), T.user("b", "second")]}

def duplicated() -> D.State:
  D.State{Nil{}, [T.user("a", "x"), T.user("b", "x")]}

def large() -> D.Value:
  D.VText{String.repeat("x", 300n)}

law success_combined_credential_empty_and_data:
  {R.finalize(T.response(), T.configuration(), empty()) == S.response_error(S.DataError{}) : S.Response}
def success_combined_credential_empty_and_data():
  {==}

law success_combined_credential_duplicated_and_data:
  {R.finalize(T.response(), T.configuration(), duplicated()) == S.response_error(S.DataError{}) : S.Response}
def success_combined_credential_duplicated_and_data():
  {==}

law refusal_discards_provisional_without_require_credentials_valid_cases:
  {R.finalize(S.Response{S.Refusal{}, D.VBool{True{}}}, T.configuration(), duplicated()) ==
    S.Response{S.Refusal{}, D.VBool{True{}}} : S.Response}
def refusal_discards_provisional_without_require_credentials_valid_cases():
  {==}

law unicode_invalid_in_response_and_data:
  {R.finalize(S.Response{S.Success{}, D.VText{SCon{Chr{55296}, SNil{}}}}, T.configuration(), T.initial()) ==
    S.response_error(S.DataError{}) : S.Response}
def unicode_invalid_in_response_and_data():
  {==}

law response_large_negative_and_truncated:
  {R.finalize(S.Response{S.Success{}, large()}, T.configuration(), T.initial()) == S.response_error(S.Limit{}) : S.Response}
def response_large_negative_and_truncated():
  {==}

law refusal_large_also_and_limit:
  {R.finalize(S.Response{S.Refusal{}, large()}, T.configuration(), empty()) == S.response_error(S.Limit{}) : S.Response}
def refusal_large_also_and_limit():
  {==}

law data_invalid_precede_limit_of_response:
  {R.finalize(S.Response{S.Success{}, large()}, T.configuration(), duplicated()) == S.response_error(S.DataError{}) : S.Response}
def data_invalid_precede_limit_of_response():
  {==}

law failure_negative_loads_diagnostic_private:
  {R.finalize(S.Response{S.Failure{}, D.VText{"secret"}}, T.configuration(), duplicated()) ==
    S.response_error(S.Failure{}) : S.Response}
def failure_negative_loads_diagnostic_private():
  {==}

law all_os_errors_and_refusals_discard_working:
  for r: S.Response
  for without_success: {U.status_success(r) == False{} : Bool}
  {S.publish(r, T.initial(), duplicated()) == T.initial() : D.State}
def all_os_errors_and_refusals_discard_working(r, without_success):
  U.all_status_without_success_preserves_published(r, T.initial(), duplicated(), without_success)

law final_negative_erases_observation_before_of_error:
  {N.snapshot(N.advance(N.Running{T.initial(),
    S.Access{D.ReadCell{D.Application{"nonexistent"}, "a", "x"}, return_value => S.Finish{D.VAbsent{}}},
    T.trace(T.initial())}, S.schema(T.configuration()))) ==
      S.Final{T.initial(), S.append(T.trace(T.initial()),
        S.OperationEvent{D.ReadCell{D.Application{"nonexistent"}, "a", "x"}, S.ErrorOfData{}}),
        S.response_error(S.DataError{})} : S.Trace}
def final_negative_erases_observation_before_of_error():
  {==}

law prefixes_later_of_terminate_negative_reexecute_reading:
  {N.traverse(12n, T.machine_final(), S.schema(T.configuration())) ==
    S.Final{T.initial(), T.trace(T.initial()), T.response()} : S.Trace}
def prefixes_later_of_terminate_negative_reexecute_reading():
  N.stopped_absorbs(12n, T.initial(), T.trace(T.initial()), T.response(), S.schema(T.configuration()))
