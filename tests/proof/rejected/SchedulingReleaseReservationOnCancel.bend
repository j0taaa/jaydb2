# Regression: setting stopped alone does not complete the reader's reservation.
import Base
import ../../../proof/FrameQueue.bend as Q
law false_cancel_releases_header_reservation_before_return:
  {Q.items(Q.cancel(Q.Queue{[], Q.Header{}, None{}, False{}})) == 0n : Nat}
def false_cancel_releases_header_reservation_before_return():
  {==}
