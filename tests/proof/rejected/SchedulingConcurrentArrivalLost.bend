# Regression: collection is not a frozen snapshot; the reader can append an
# eligible head between select_if calls and that completed reception is kept.
import Base
import ../../../proof/FrameQueue.bend as Q
import ../../../proof/ReadBatchCollection.bend as C
law false_concurrent_arrival_is_absent_from_the_batch:
  {C.batch(C.run(frame => True{}, Q.Bounds{2n, 0n},
    [C.Produce{C.ReserveBody{0n}}, C.Produce{C.CommitBody{Q.Frame{0n, []}}}, C.TryCandidate{}],
    C.seed(Q.Queue{[], Q.Header{}, None{}, False{}}, 1n))) == [] : List<&2, Q.Frame>}
def false_concurrent_arrival_is_absent_from_the_batch():
  {==}
