# Deliberately false input-content claim; must reject at the proof body.
import Base
import ../../../library/Key.bend as K
import ../../../library/IndexSourceRows.bend as Source



law false_reject_duplicate_source_keys_have_unique_input_domain:
  {Source.unique([Source.SourceEntry{K.encode(["v"]),["v"],"first"},Source.SourceEntry{K.encode(["v"]),["v"],"last"}]) == True{} : Bool}
def false_reject_duplicate_source_keys_have_unique_input_domain(): {==}
