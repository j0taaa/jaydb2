import Base
import ../../../contract/Data.bend as D
import ../../../contract/Logic.bend as L
import ../../../library/Value.bend as V
import ../../../library/Key.bend as Key
import ../../../library/Record.bend as Record
import ../../../library/Query.bend as Query
import ../../../library/Sequence.bend as Sequence
import ../../../library/ValueScalarProofs.bend as Scalar
import ../../../library/ValueListProofs.bend as Lists
import ../../../library/RecordCanonicalProofs.bend as Canonical
import ../../../library/RecordLookupProofs.bend as FieldLookup

def surrogate() -> String: SCon{Chr{55296},SNil{}}

law false:
  {Record.make([D.Field{"a",D.VAbsent{}},D.Field{"a",D.VAbsent{}}]) == Some{D.VRecord{"a",D.VAbsent{},D.VRecord{"a",D.VAbsent{},D.VRecordEmpty{}}}} : Maybe<&2,D.Value>}
def false(): {==}
