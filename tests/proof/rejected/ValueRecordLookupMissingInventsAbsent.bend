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

law false_negative_missing_field_is_a_present_absent_value:
  {Query.field(Record.raw([D.Field{"a",D.VAbsent{}}]),"b") == Some{D.VAbsent{}} : Maybe<&2,D.Value>}
def false_negative_missing_field_is_a_present_absent_value(): {==}
