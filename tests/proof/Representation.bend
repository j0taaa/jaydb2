import Base
import ../../contract/Data.bend as D
import ../../contract/Protocol.bend as P
import ../../contract/Logic.bend as L
import ../../src/State.bend as E
import ../../src/Request.bend as Q
import ../../proof/Representation.bend as R
import ../../proof/Authentication.bend as A
import ./Certificate.bend as T

def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"Things", "key", [
    D.Column{"key", D.TextValue{}, False{}}, D.Column{"flag", D.Boolean{}, True{}},
    D.Column{"n", D.Integer{}, False{}}, D.Column{"text", D.TextValue{}, True{}}]}]}

def state() -> D.State:
  D.State{[D.Table{"Things", [
    D.Row{"a", [D.Field{"key", D.VText{"a"}}, D.Field{"flag", D.VAbsent{}},
      D.Field{"n", D.VInt{2147483648, 0}}, D.Field{"text", D.VText{"é"}}]},
    D.Row{"é", [D.Field{"key", D.VText{"é"}}, D.Field{"flag", D.VBool{False{}}},
      D.Field{"n", D.VInt{2147483647, 4294967295}}, D.Field{"text", D.VAbsent{}}]}]}],
    [T.user("a", "c1"), T.user("aa", "c2"), T.user("é", "c3")]}

law structure_of_sample:
  {D.structure(schema(), state()) == True{} : Bool}
def structure_of_sample():
  {==}

law roundtrip_without_lose_absence_unicode_neither_bits:
  {E.decode(D.state_value(state()), schema()) == Some{state()} : Maybe<&2, D.State>}
def roundtrip_without_lose_absence_unicode_neither_bits():
  R.transport_private_preserves_state(schema(), state(), structure_of_sample())

law output_of_transport_structured:
  {D.structure(schema(), state()) == True{} : Bool}
def output_of_transport_structured():
  R.transport_private_only_returns_state_structured(D.state_value(state()), schema(), state(), roundtrip_without_lose_absence_unicode_neither_bits())

law context_of_user_in_end_of_registry:
  {D.context_present(state(), D.Context{"é", "person"}) == True{} : Bool}
def context_of_user_in_end_of_registry():
  A.authentication_implies_context_present(schema(), state(), "c3", D.Context{"é", "person"}, structure_of_sample(), {==})

law credential_empty_negative_authenticates:
  {D.authenticate(state(), "") == None{} : Maybe<&2, D.Context>}
def credential_empty_negative_authenticates():
  A.state_publishable_negative_authenticates_empty(schema(), state(), structure_of_sample())

def request() -> P.Request:
  P.Request{"c3", "\"\\n\n𝄞", D.VList{D.VInt{4294967295, 4294967295}, D.VList{D.VAbsent{}, D.VListEmpty{}}}, "π\n\\"}

law envelope_preserves_source_proof_and_arguments:
  {Q.extract(P.request_value(request())) == Some{request()} : Maybe<&2, P.Request>}
def envelope_preserves_source_proof_and_arguments():
  R.request_is_valid_preserves_all_os_fields(request(), {==})

law envelope_extracted_and_exactly_o_original:
  {P.request_value(request()) == P.request_value(request()) : D.Value}
def envelope_extracted_and_exactly_o_original():
  R.envelope_accepted_reconstructs_exactly(P.request_value(request()), request(), {==})

law envelope_accepted_also_and_valid:
  {D.value_valid(P.request_value(request())) == True{} : Bool}
def envelope_accepted_also_and_valid():
  L.and_left(
    {D.value_valid(P.request_value(request())) == True{} : Bool},
    {P.request_value(request()) == P.request_value(request()) : D.Value},
    R.extract_preserves_value_and_is_valid(P.request_value(request()), request(), envelope_preserves_source_proof_and_arguments()))
