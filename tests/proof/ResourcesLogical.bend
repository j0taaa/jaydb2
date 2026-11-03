# Logical boundaries of revised configuration, without an artificial Environment.
import Base
import ../../contract/Data.bend as D
import ../../contract/Semantics.bend as S
import ../../contract/Protocol.bend as P
import ../../contract/Bytes.bend as B
import ../../contract/Requirements.bend as R
import ../../contract/Resources.bend as X

law three_sizes_zero_in_message_and_state_are_allowed:
  {R.limits_all_valid(S.Limits{0n, 0n, 256n}) == True{} : Bool}
def three_sizes_zero_in_message_and_state_are_allowed():
  {==}

law response_needs_behave_os_errors:
  {R.limits_all_valid(S.Limits{1024n, 1024n, 0n}) == False{} : Bool}
def response_needs_behave_os_errors():
  {==}

law message_exactly_in_ceiling_and_admitted:
  {X.decide_reception_in(S.Limits{1n, 0n, 256n}, X.BodyReceived{0, 1, [0]}) ==
    X.ProcessBody{[0]} : X.Disposition}
def message_exactly_in_ceiling_and_admitted():
  {==}

law message_above_of_ceiling_closes_combined_limit:
  {X.decide_reception_in(S.Limits{1n, 0n, 256n}, X.BodyReceived{0, 2, [0, 0]}) ==
    X.RefuseClose{S.Limit{}} : X.Disposition}
def message_above_of_ceiling_closes_combined_limit():
  {==}

def bytes_result(r: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match r:
    case None{}:
      Nil{}
    case Some{bs}:
      bs

def state() -> D.State:
  D.State{Nil{}, Nil{}}

def size_state() -> Nat:
  B.length(bytes_result(P.encode(D.state_value(state()))))

def configuration(ceiling: Nat) -> S.Configuration:
  S.Configuration{D.Schema{Nil{}}, S.NoneLaw{}, S.Limits{0n, ceiling, 256n}, "tests-three-limits"}

law state_exactly_in_ceiling_preserves_validity_structural:
  {R.structure(configuration(size_state()), state()) == True{} : Bool}
def state_exactly_in_ceiling_preserves_validity_structural():
  {==}

law state_one_byte_above_of_ceiling_continues_invalid:
  {R.structure(configuration(Nat.sub(size_state(), 1n)), state()) == False{} : Bool}
def state_one_byte_above_of_ceiling_continues_invalid():
  {==}
