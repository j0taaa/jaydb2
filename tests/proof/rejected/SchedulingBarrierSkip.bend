# Regression: an already queued exclusive barrier stops collection at its head.
import Base
import ../../../proof/FrameQueue.bend as Q
import ../../../proof/ReadBatchSelection.bend as B

def eligible(frame: Q.Frame) -> Bool:
  match frame:
    case Q.Frame{0n, body}: False{}
    case Q.Frame{1n+identity, body}: True{}

law false_read_collection_can_skip_the_barrier:
  {B.selected(B.collect(eligible, 2n,
    Q.Queue{[Q.Frame{0n, []}, Q.Frame{1n, []}], Q.Idle{}, None{}, False{}})) ==
    [Q.Frame{1n, []}] : List<&2, Q.Frame>}
def false_read_collection_can_skip_the_barrier():
  {==}
