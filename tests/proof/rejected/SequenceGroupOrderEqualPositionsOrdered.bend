import Base
import ../../../contract/Data.bend as D
import ../../../library/Sequence.bend as Sequence
import ../../../library/SequenceLastSource.bend as Last
import ../../../library/SequenceGroupOrder.bend as Order
import ../../../library/SequenceGroupUniqueness.bend as U

def key(value: D.Value) -> String:
  match value:
    case D.VText{s}: s
    case _: ""

law false_negative_last_position_order_can_be_nonstrict:
  Order.Greater(Some{1n},Some{1n})
def false_negative_last_position_order_can_be_nonstrict(): {==}
