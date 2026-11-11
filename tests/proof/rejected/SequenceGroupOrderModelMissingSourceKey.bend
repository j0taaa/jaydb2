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

law false:
  Order.Ordered(~key,[D.VText{"a"}],[Sequence.Group{"z",[D.VText{"z"}]}])
def false():
  U.Both{Order.Located{0n,{==}},U.Both{Unit{},Unit{}}}
