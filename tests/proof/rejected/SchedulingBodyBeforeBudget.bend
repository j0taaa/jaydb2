# Regression: no body allocation/read reservation before byte budget exists.
import Base
import ../../../proof/FrameQueue.bend as Q
law false_one_byte_body_can_be_reserved_with_zero_budget:
  {Q.reserve_body(Q.Bounds{1n, 0n}, Q.Queue{[], Q.Header{}, None{}, False{}}, 1n) ==
    Some{Q.Queue{[], Q.Body{1n}, None{}, False{}}} : Maybe<&2, Q.Queue>}
def false_one_byte_body_can_be_reserved_with_zero_budget():
  {==}
