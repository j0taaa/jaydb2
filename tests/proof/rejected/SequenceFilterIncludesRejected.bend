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

law false:
  {Sequence.filter(~accept_bool,[D.VBool{False{}},D.VBool{True{}}]) == [D.VBool{False{}},D.VBool{True{}}] : List<&2,D.Value>}
def false(): {==}
