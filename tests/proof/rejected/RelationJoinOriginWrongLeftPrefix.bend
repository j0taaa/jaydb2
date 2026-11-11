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

law false:
  Model.Origin(~key,~key,False{},[item("a","L1"),item("a","L2")],[item("a","R1")],0n,Rows.pair(item("a","L2"),item("a","R1")))
def false():
  Tuple{1n,Tuple{item("a","L2"),Tuple{0n,L.Both{{==},L.Both{Tuple{0n,Tuple{item("a","R1"),L.Both{{==},L.Both{{==},L.Both{{==},{==}}}}}},L.Both{{==},{==}}}}}}}
