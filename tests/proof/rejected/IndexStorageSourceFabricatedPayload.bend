# Deliberately false source/domain/indexed-content claim. Proof-body failure.
import Base
import ../../../library/IndexSourceRows.bend as Source
import ../../../library/IndexSourceProjection.bend as Projection
import ../../../contract/Data.bend as D

def e(key: String,parts: List<&2,String>,target: String) -> Source.SourceEntry: Source.SourceEntry{key,parts,target}

def matching() -> Source.SourceEntry: e("a",["yes"],"target")

law false_reject_source_fabricated_payload:
  Projection.Origin<["yes"],[matching()],0n,D.VText{"other"}>
def false_reject_source_fabricated_payload(): Projection.SourceOrigin{0n,matching(),{==},{==},{==},{==}}
