# Deliberately false source/domain/indexed-content claim. Proof-body failure.
import Base
import ../../../library/IndexSourceRows.bend as Source
import ../../../library/IndexSourceProjection.bend as Projection
import ../../../library/Key.bend as K

def e(key: String,parts: List<&2,String>,target: String) -> Source.SourceEntry: Source.SourceEntry{key,parts,target}

def matching() -> Source.SourceEntry: e("a",["yes"],"target")

law false_reject_source_reversed_matching_rank_order:
  {Nat.is_lt(Projection.before([matching(),e("b",["yes"],"last")],1n,K.encode(["yes"])),Projection.before([matching(),e("b",["yes"],"last")],0n,K.encode(["yes"]))) == True{} : Bool}
def false_reject_source_reversed_matching_rank_order(): {==}
