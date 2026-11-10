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

law false_negative_text_decoder_accepts_surrogate_char_data:
  {V.text(D.VText{surrogate()}) == Some{surrogate()} : Maybe<&2,String>}
def false_negative_text_decoder_accepts_surrogate_char_data(): {==}
