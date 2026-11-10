import Base
import ../../../contract/Data.bend as D
import ../../../library/Sequence.bend as Sequence
import ../../../library/SequencePaginationProofs.bend as Position
import ../../../library/SequenceFilterProofs.bend as Filter

def accept_none(v: D.Value) -> Bool: False{}
law false_negative_filter_rank_strictness_needs_no_matching_predicate:
  {Nat.is_lt(Filter.before(~accept_none,[D.VText{"a"},D.VText{"b"}],0n),Filter.before(~accept_none,[D.VText{"a"},D.VText{"b"}],1n)) == True{} : Bool}
def false_negative_filter_rank_strictness_needs_no_matching_predicate(): {==}
