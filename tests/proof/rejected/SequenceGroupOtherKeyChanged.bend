import Base
import ../../../contract/Data.bend as D
import ../../../library/Sequence.bend as Sequence
import ../../../library/SequenceGroupLookup.bend as Lookup
import ../../../library/SequenceGroupUniqueness.bend as U

def item(key: String,name: String) -> D.Value:
  D.VRecord{"key",D.VText{key},D.VRecord{"id",D.VText{name},D.VRecordEmpty{}}}
def key(value: D.Value) -> String:
  match value:
    case D.VRecord{"key",D.VText{name},tail}: name
    case _: ""

law false:
  {Lookup.lookup("b",Sequence.group_insert("a",item("a","1"),[Sequence.Group{"b",[item("b","x")]}])) == Some{[item("a","1"),item("b","x")]} : Maybe<&2,List<&2,D.Value>>}
def false(): {==}
