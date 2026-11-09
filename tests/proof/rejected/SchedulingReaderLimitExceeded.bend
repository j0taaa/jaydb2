# Regression: repeated attempts cannot collect beyond the fixed batch capacity.
import Base
import ../../../proof/FrameQueue.bend as Q
import ../../../proof/ReadBatchCollection.bend as C
law false_second_head_is_collected_after_capacity_is_exhausted:
  {C.batch(C.run(frame => True{}, Q.Bounds{2n, 0n}, [C.TryCandidate{}, C.TryCandidate{}],
    C.seed(Q.Queue{[Q.Frame{0n, []}, Q.Frame{1n, []}], Q.Idle{}, None{}, False{}}, 1n))) ==
      [Q.Frame{0n, []}, Q.Frame{1n, []}] : List<&2, Q.Frame>}
def false_second_head_is_collected_after_capacity_is_exhausted():
  {==}
