# Deliberately false source/domain/indexed-content claim. Proof-body failure.
import Base
import ../../../library/IndexSourceRows.bend as Source
import ../../../library/IndexSourceContent.bend as Content
import ../../../library/Key.bend as K
import ../../../library/Sequence.bend as Sequence

def e(key: String,parts: List<&2,String>,target: String) -> Source.SourceEntry: Source.SourceEntry{key,parts,target}

law false_reject_source_deduplicated_targets:
  {Sequence.length(Content.targets([e("a",["yes"],"same"),e("b",["yes"],"same")],K.encode(["yes"]))) == 1n : Nat}
def false_reject_source_deduplicated_targets(): {==}
