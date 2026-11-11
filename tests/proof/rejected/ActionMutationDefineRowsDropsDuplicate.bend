# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../library/MutationPrefixProofs.bend as Prefix
import ../../../library/MutationBooleanDecisions.bend as Boolean
import ../../../library/ReadPrefix.bend as Cut
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Action.bend as A

def collection() -> D.Collection: D.Application{"t"}

def row(+key: String,title: String) -> D.Row:
  D.Row{key,[D.Field{"id",D.VText{key}},D.Field{"title",D.VText{title}}]}

law false:
  {Cut.cut(~Unit,~Prefix.unit_return,Unit{},2n,0n,A.define_rows(collection(),[row("k","first"),row("k","first")],S.Finish{D.VAbsent{}})) == Cut.prefix([D.DefineRow{collection(),D.row_key(row("k","first")),Boolean.row_fields(row("k","first"))}],S.Finish{D.VAbsent{}}) : Cut.Prefix}
def false(): {==}
