# Regression: failed delivery does not cancel mandatory joins of later handles.
import Base
import ../../../proof/FrameQueue.bend as Q
import ../../../proof/ReadBatchExecution.bend as B
law false_delivery_error_skips_remaining_joins:
  {B.joined_jobs(B.joins(B.drain(job => B.Joined{[]},
    job => response => B.SendError{[], "write failed"},
    [Q.Frame{0n, []}, Q.Frame{1n, []}], None{}))) == [Q.Frame{0n, []}] : List<&2, Q.Frame>}
def false_delivery_error_skips_remaining_joins():
  {==}
