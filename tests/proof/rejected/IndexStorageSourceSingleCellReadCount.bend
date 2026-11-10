# Deliberately false source/domain/indexed-content claim. Proof-body failure.
import Base
import ../../../library/IndexSourceRows.bend as Source
import ../../../library/IndexSourceContent.bend as Content
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S

def e(key: String,parts: List<&2,String>,target: String) -> Source.SourceEntry: Source.SourceEntry{key,parts,target}

def collection() -> D.Collection: D.Application{"index"}

def matching() -> Source.SourceEntry: e("a",["yes"],"target")

law false_reject_source_single_cell_read_count:
  {List.length(&2,S.OperationEvent,Content.events([matching()],collection())) == 1n : Nat}
def false_reject_source_single_cell_read_count(): {==}
