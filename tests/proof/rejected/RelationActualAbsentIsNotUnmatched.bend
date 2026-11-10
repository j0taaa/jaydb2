import Base
import ../../../contract/Data.bend as D
import ../../../contract/Logic.bend as L
import ../../../library/Relation.bend as Relation
import ../../../library/RelationRows.bend as Rows
import ../../../library/RelationNoMatches.bend as N
import ../../../library/RelationOuterRows.bend as Outer

def item(key: String,name: String) -> D.Value:
  D.VRecord{"key",D.VText{key},D.VRecord{"id",D.VText{name},D.VRecordEmpty{}}}
def key(value: D.Value) -> String:
  match value:
    case D.VRecord{"key",D.VText{name},tail}: name
    case _: ""
def same(value: D.Value) -> String: "a"

law false_negative_actual_matching_absent_value_is_an_unmatched_placeholder:
  Outer.Origin(~same,~same,item("a","L"),[D.VAbsent{}],0n,Rows.pair(item("a","L"),D.VAbsent{}))
def false_negative_actual_matching_absent_value_is_an_unmatched_placeholder():
  L.Right{N.Both{{==},N.Both{{==},{==}}}}
