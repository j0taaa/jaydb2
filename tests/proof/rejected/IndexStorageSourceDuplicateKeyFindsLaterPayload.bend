# Deliberately false source/domain/indexed-content claim. Proof-body failure.
import Base
import ../../../library/IndexSourceRows.bend as Source
import ../../../contract/Data.bend as D

def e(key: String,parts: List<&2,String>,target: String) -> Source.SourceEntry: Source.SourceEntry{key,parts,target}

law false_reject_source_duplicate_key_finds_later_payload:
  {D.find_row(Source.rows([e("a",["first"],"first"),e("a",["second"],"second")]),"a") == Some{Source.raw(e("a",["second"],"second"))} : Maybe<&2,D.Row>}
def false_reject_source_duplicate_key_finds_later_payload(): {==}
