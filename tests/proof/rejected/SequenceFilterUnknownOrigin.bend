import Base
import ../../../contract/Data.bend as D
import ../../../library/Sequence.bend as Sequence
import ../../../library/SequencePaginationProofs.bend as Position
import ../../../library/SequenceFilterProofs.bend as Filter
import ../../../contract/Logic.bend as L

def accept_all(v: D.Value) -> Bool: True{}
def accept_bool(v: D.Value) -> Bool:
  match v:
    case D.VBool{b}: b
    case _: False{}

law false:
  Filter.Origin(~accept_all,[D.VText{"a"}],0n,D.VText{"b"})
def false():
  Tuple{0n,L.Both{{==},L.Both{{==},{==}}}}
