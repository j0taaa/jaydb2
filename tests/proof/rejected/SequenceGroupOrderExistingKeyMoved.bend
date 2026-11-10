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

law false_negative_updating_an_existing_group_moves_it_to_the_end:
  {Sequence.group(~key,[D.VText{"a"},D.VText{"b"},D.VText{"a"}]) == [Sequence.Group{"b",[D.VText{"b"}]},Sequence.Group{"a",[D.VText{"a"},D.VText{"a"}]}] : List<&2,Sequence.Group>}
def false_negative_updating_an_existing_group_moves_it_to_the_end(): {==}
