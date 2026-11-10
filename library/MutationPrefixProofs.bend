# Owned CPS prefix under the specified supplied UnitValue stream. This makes
# no claim that real primitive operations succeed; WriteTrace handles their
# actual input-dependent Changed/FailureData behavior separately. Arbitrary
# caller actions are retained exactly at the cut, including reads/writes.
import Base
import ./MutationWriteSequence.bend as W
import ./MutationWritePlan.bend as M
import ./ReadPrefix.bend as Cut
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S

def unit_return(env: Unit,index: Nat) -> S.Return: S.UnitValue{}

law successful_write_callbacks_issue_exactly_the_owned_ordered_prefix_then_handoff:
  for +operations: List<&2,D.Operation>
  for +index: Nat
  for -done: S.Action
  {Cut.cut(~Unit,~unit_return,Unit{},M.depth(operations,0n),index,W.perform(operations,done)) == Cut.prefix(operations,done) : Cut.Prefix}
def successful_write_callbacks_issue_exactly_the_owned_ordered_prefix_then_handoff(operations,index,done):
  match operations:
    case Nil{}: {==}
    case Con{+op,+tail}:
      Equal.cong(Cut.Prefix,Cut.Prefix,prefix => Cut.More{op,prefix},Cut.cut(~Unit,~unit_return,Unit{},M.depth(tail,0n),1n+index,W.perform(tail,done)),Cut.prefix(tail,done),successful_write_callbacks_issue_exactly_the_owned_ordered_prefix_then_handoff(tail,1n+index,done))
