import Base
import ../../../contract/Data.bend as D
import ../../../library/Sequence.bend as Sequence
import ../../../library/SortProof.bend as Sort
import ../../../library/SequenceStabilityProofs.bend as Stable

def completed(name: String) -> D.Value:
  D.VRecord{"completed",D.VBool{True{}},D.VRecord{"id",D.VText{name},D.VRecordEmpty{}}}
def incomplete(name: String) -> D.Value:
  D.VRecord{"completed",D.VBool{False{}},D.VRecord{"id",D.VText{name},D.VRecordEmpty{}}}
def never_less(a: D.Value,b: D.Value) -> Bool: False{}
def always_less(a: D.Value,b: D.Value) -> Bool: True{}
def all(v: D.Value) -> Bool: True{}

law false:
  {Sequence.sort(~Sort.completed_less,[incomplete("a"),completed("x"),incomplete("b")]) == [incomplete("b"),incomplete("a"),completed("x")] : List<&2,D.Value>}
def false(): {==}
