# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../library/MutationPrefixProofs.bend as Prefix
import ../../../library/ReadPrefix.bend as Cut
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Mutation.bend as M

def collection() -> D.Collection: D.Application{"t"}

law false_reject_columns_reordering:
  {Cut.cut(~Unit,~Prefix.unit_return,Unit{},2n,0n,M.columns(collection(),"k",[D.Field{"a",D.VAbsent{}},D.Field{"b",D.VAbsent{}}],S.Finish{D.VAbsent{}})) == Cut.prefix([D.DefineColumn{collection(),"k","b",D.VAbsent{}},D.DefineColumn{collection(),"k","a",D.VAbsent{}}],S.Finish{D.VAbsent{}}) : Cut.Prefix}
def false_reject_columns_reordering(): {==}
