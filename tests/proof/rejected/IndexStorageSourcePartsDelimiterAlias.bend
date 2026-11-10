# Deliberately false source/domain/indexed-content claim. Proof-body failure.
import Base
import ../../../library/IndexSourceRows.bend as Source
import ../../../library/IndexSourceContent.bend as Content
import ../../../library/Key.bend as K

def e(key: String,parts: List<&2,String>,target: String) -> Source.SourceEntry: Source.SourceEntry{key,parts,target}

law false_reject_source_parts_delimiter_alias:
  {Content.matches(K.encode(["a","b"]),e("a",["a|b"],"t")) == True{} : Bool}
def false_reject_source_parts_delimiter_alias(): {==}
