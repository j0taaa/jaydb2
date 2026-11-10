import Base
import ../../../contract/Data.bend as D
import ../../../library/Sequence.bend as Sequence
import ../../../library/SequenceLastSource.bend as Last
import ../../../library/SequenceGroupOrder.bend as Order
import ../../../library/SequenceGroupUniqueness.bend as U
import ../../../contract/Logic.bend as L

def key(value: D.Value) -> String:
  match value:
    case D.VText{s}: s
    case _: ""

law false_negative_first_matching_position_satisfies_greatest_position_meaning:
  Last.Maximal(~key,"a",[D.VText{"a"},D.VText{"b"},D.VText{"a"}],0n)
def false_negative_first_matching_position_satisfies_greatest_position_meaning():
  Tuple{D.VText{"a"},L.Both{{==},L.Both{{==},+index => +value => present => matched => {==}}}}
