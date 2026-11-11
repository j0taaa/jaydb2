import Base
import ../../../contract/Logic.bend as L
import ../../../contract/Data.bend as D
import ../../../library/Sequence.bend as Sequence
import ../../../library/SequencePaginationProofs.bend as Position
import ../../../library/SequenceFilterProofs.bend as Filter

def accept_all(v: D.Value) -> Bool: True{}
def accept_bool(v: D.Value) -> Bool:
  match v:
    case D.VBool{b}: b
    case _: False{}

law false:
  Filter.Origin(~accept_all,[D.VText{"a"},D.VText{"b"}],0n,D.VText{"b"})
def false():
  Tuple{1n,L.Both{{==},L.Both{{==},{==}}}}
