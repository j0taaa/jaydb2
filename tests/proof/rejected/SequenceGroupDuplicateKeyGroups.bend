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

law false_negative_groups_can_split_one_key_into_two_entries:
  {Sequence.group(~key,[item("a","1"),item("a","2")]) == [Sequence.Group{"a",[item("a","1")]},Sequence.Group{"a",[item("a","2")]}] : List<&2,Sequence.Group>}
def false_negative_groups_can_split_one_key_into_two_entries(): {==}
