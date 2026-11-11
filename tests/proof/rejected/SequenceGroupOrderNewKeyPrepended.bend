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
  {Sequence.group(~key,[D.VText{"z"},D.VText{"a"},D.VText{"b"}]) == [Sequence.Group{"z",[D.VText{"z"}]},Sequence.Group{"b",[D.VText{"b"}]},Sequence.Group{"a",[D.VText{"a"}]}] : List<&2,Sequence.Group>}
def false(): {==}
