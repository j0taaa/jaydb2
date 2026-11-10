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

law false_negative_last_measure_can_hide_a_matching_source_occurrence:
  {Last.last(~key,"a",[D.VText{"a"}]) == None{} : Maybe<&2,Nat>}
def false_negative_last_measure_can_hide_a_matching_source_occurrence(): {==}
