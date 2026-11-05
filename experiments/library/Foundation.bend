import Base
import ../../library/Value.bend as V
import ../../library/Int64.bend as I
import ../../library/Record.bend as R
import ../../library/Key.bend as K
import ../../library/Laws.bend as L
import ../../contract/Data.bend as D

law carry:
  {I.add(V.Int64{0, 4294967295}, V.Int64{0, 1}) == Some{V.Int64{1, 0}} : Maybe<&2, V.Int64>}
def carry(): {==}
law borrow:
  {I.sub(V.Int64{1, 0}, V.Int64{0, 1}) == Some{V.Int64{0, 4294967295}} : Maybe<&2, V.Int64>}
def borrow(): {==}
law max_overflow:
  {I.increment(V.Int64{2147483647, 4294967295}) == None{} : Maybe<&2, V.Int64>}
def max_overflow(): {==}
law min_overflow:
  {I.decrement(V.Int64{2147483648, 0}) == None{} : Maybe<&2, V.Int64>}
def min_overflow(): {==}
law min_plus_max:
  {I.add(V.Int64{2147483648, 0}, V.Int64{2147483647, 4294967295}) == Some{V.Int64{4294967295, 4294967295}} : Maybe<&2, V.Int64>}
def min_plus_max(): {==}
law signed_order:
  {I.lt(V.Int64{2147483648, 0}, V.Int64{0, 0}) == True{} : Bool}
def signed_order(): {==}
law canonical_record:
  {R.make([D.Field{"a", D.VAbsent{}}, D.Field{"z", D.VInt{2147483648, 0}}]) == Some{D.VRecord{"a", D.VAbsent{}, D.VRecord{"z", D.VInt{2147483648, 0}, D.VRecordEmpty{}}}} : Maybe<&2, D.Value>}
def canonical_record(): {==}
law duplicate_rejected:
  {R.make([D.Field{"a", D.VAbsent{}}, D.Field{"a", D.VAbsent{}}]) == None{} : Maybe<&2, D.Value>}
def duplicate_rejected(): {==}
law key_delimiters:
  {K.decode(K.encode(["", "ce:pz", "á"])) == Some{["", "ce:pz", "á"]} : Maybe<&2, List<&2, String>>}
def key_delimiters(): {==}
law key_trailing_rejected:
  {K.decode("zz") == None{} : Maybe<&2, List<&2, String>>}
def key_trailing_rejected(): {==}
