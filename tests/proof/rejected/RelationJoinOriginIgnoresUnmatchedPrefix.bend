import Base
import ../../../contract/Data.bend as D
import ../../../contract/Logic.bend as L
import ../../../library/Relation.bend as Relation
import ../../../library/RelationRows.bend as Rows
import ../../../library/RelationModel.bend as Model

def item(key: String,name: String) -> D.Value:
  D.VRecord{"key",D.VText{key},D.VRecord{"id",D.VText{name},D.VRecordEmpty{}}}
def key(value: D.Value) -> String:
  match value:
    case D.VRecord{"key",D.VText{name},tail}: name
    case _: ""

law false_negative_left_origin_can_ignore_a_preceding_unmatched_left_occurrence:
  Model.Origin(~key,~key,True{},[item("b","M"),item("a","L1")],[item("a","R1")],0n,Rows.pair(item("a","L1"),item("a","R1")))
def false_negative_left_origin_can_ignore_a_preceding_unmatched_left_occurrence():
  Tuple{1n,Tuple{item("a","L1"),Tuple{0n,L.Both{{==},L.Both{L.Left{Tuple{0n,Tuple{item("a","R1"),L.Both{{==},L.Both{{==},L.Both{{==},{==}}}}}}},L.Both{{==},{==}}}}}}}
