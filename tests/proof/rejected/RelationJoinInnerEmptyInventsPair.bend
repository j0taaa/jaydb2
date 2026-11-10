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

law false_negative_inner_join_can_emit_without_a_left_source:
  {Relation.inner(~key,~key,[],[item("a","R1")]) == [Rows.pair(item("a","L1"),item("a","R1"))] : List<&2,D.Value>}
def false_negative_inner_join_can_emit_without_a_left_source(): {==}
