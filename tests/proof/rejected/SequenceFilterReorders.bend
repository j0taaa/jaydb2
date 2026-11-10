import Base
import ../../../contract/Data.bend as D
import ../../../library/Sequence.bend as Sequence
import ../../../library/SequencePaginationProofs.bend as Position
import ../../../library/SequenceFilterProofs.bend as Filter

def accept_all(v: D.Value) -> Bool: True{}
def accept_bool(v: D.Value) -> Bool:
  match v:
    case D.VBool{b}: b
    case _: False{}

law false_negative_filter_can_reverse_matching_occurrences:
  {Sequence.filter(~accept_all,[D.VText{"a"},D.VText{"b"}]) == [D.VText{"b"},D.VText{"a"}] : List<&2,D.Value>}
def false_negative_filter_can_reverse_matching_occurrences(): {==}
