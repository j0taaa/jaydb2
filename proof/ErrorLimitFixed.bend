# Bytes preprepared by the C boundary, compared with the ORIGINAL encoder.
# Receives no codec equivalence as a premise.
import Base
import ../contract/Semantics.bend as S
import ../contract/Protocol.bend as P

def bytes() -> List<&2, U32>:
  [0, 0, 0, 0, 0, 0, 0, 53, 6, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 6, 115, 116, 97, 116, 117, 115, 4, 0, 0, 0, 0, 0, 0, 0, 5, 108, 105, 109, 105, 116, 4, 0, 0, 0, 0, 0, 0, 0, 5, 118, 97, 108, 117, 101, 0]

law error_limit_prepared_and_exactly_to_message_original:
  {P.frame(S.response_value(S.response_error(S.Limit{}))) == Some{bytes()} : Maybe<&2, List<&2, U32>>}
def error_limit_prepared_and_exactly_to_message_original():
  {==}
