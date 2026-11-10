# Exact concatenation of owned operation prefixes. Prefix is affine Type;
# helper equality indices are erased and only DATA operation lists are copied.
import Base
import ./ReadPrefix.bend as Cut
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S

def append(first: List<&2,D.Operation>,later: List<&2,D.Operation>) -> List<&2,D.Operation>:
  match first:
    case Nil{}: later
    case Con{op,tail}: Con{op,append(tail,later)}

def attach(first: List<&2,D.Operation>,later: Cut.Prefix) -> Cut.Prefix:
  match first:
    case Nil{}: later
    case Con{operation,tail}: Cut.More{operation,attach(tail,later)}

law attaching_known_prefixes_preserves_exact_list_concatenation:
  for +first: List<&2,D.Operation>
  for +later: List<&2,D.Operation>
  for -remaining: S.Action
  {attach(first,Cut.prefix(later,remaining)) == Cut.prefix(append(first,later),remaining) : Cut.Prefix}
def attaching_known_prefixes_preserves_exact_list_concatenation(first,later,remaining):
  match first:
    case Nil{}: {==}
    case Con{+operation,+tail}:
      Equal.cong(Cut.Prefix,Cut.Prefix,prefix => Cut.More{operation,prefix},attach(tail,Cut.prefix(later,remaining)),Cut.prefix(append(tail,later),remaining),attaching_known_prefixes_preserves_exact_list_concatenation(tail,later,remaining))
