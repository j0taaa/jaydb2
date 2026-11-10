# Deliberately false source/domain/indexed-content claim. Proof-body failure.
import Base
import ../../../library/IndexSourceRows.bend as Source
import ../../../library/IndexSourceProjection.bend as Projection
import ../../../library/Key.bend as K

def e(key: String,parts: List<&2,String>,target: String) -> Source.SourceEntry: Source.SourceEntry{key,parts,target}

law false_reject_source_wrong_prefix_rank:
  {Projection.before([e("a",["yes"],"a"),e("b",["no"],"b"),e("c",["yes"],"c")],2n,K.encode(["yes"])) == 0n : Nat}
def false_reject_source_wrong_prefix_rank(): {==}
