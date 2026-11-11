# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../library/MutationPrefixProofs.bend as Prefix
import ../../../library/ReadPrefix.bend as Cut
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Mutation.bend as M

def collection() -> D.Collection: D.Application{"t"}

law false:
  {Cut.cut(~Unit,~Prefix.unit_return,Unit{},2n,0n,M.remove_rows(collection(),["a","b"],S.Finish{D.VAbsent{}})) == Cut.prefix([D.RemoveRow{collection(),"b"},D.RemoveRow{collection(),"a"}],S.Finish{D.VAbsent{}}) : Cut.Prefix}
def false(): {==}
