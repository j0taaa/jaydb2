# Regression: setting stopped alone does not complete the reader's reservation.
import Base
import ../../../proof/FrameQueue.bend as Q
law false:
  {Q.items(Q.cancel(Q.Queue{[], Q.Header{}, None{}, False{}})) == 0n : Nat}
def false():
  {==}
