# Regression: even a zero-byte frame occupies one bounded queue item.
import Base
import ../../../proof/FrameQueue.bend as Q
law false_empty_body_has_no_item_cost:
  {Q.items(Q.Queue{[Q.Frame{0n, []}], Q.Header{}, None{}, False{}}) == 1n : Nat}
def false_empty_body_has_no_item_cost():
  {==}
