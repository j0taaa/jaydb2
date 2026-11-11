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

law false:
  Last.Maximal(~key,"a",[D.VText{"a"},D.VText{"b"},D.VText{"a"}],0n)
def false():
  Tuple{D.VText{"a"},L.Both{{==},L.Both{{==},+index => +value => present => matched => {==}}}}
