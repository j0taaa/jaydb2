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

law false_negative_page_length_is_always_the_requested_size:
  {Sequence.length(Sequence.page(1n,10n,[D.VText{"a"},D.VText{"b"},D.VText{"c"}])) == 10n : Nat}
def false_negative_page_length_is_always_the_requested_size(): {==}
