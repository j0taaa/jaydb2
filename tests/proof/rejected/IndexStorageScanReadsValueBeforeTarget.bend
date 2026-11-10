# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../library/IndexEntryProofs.bend as Entry
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Index.bend as I
import ../../../library/Key.bend as K
import ../../../src/Termination.bend as T

def collection() -> D.Collection: D.Application{"index"}

def schema() -> D.Schema: D.Schema{[Entry.schema("index")]}

def entry(key: String,tag: String,target: String) -> D.Row: I.entry(key,[tag],target)

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"index",rows}],Nil{}}

def done(value: D.Value) -> S.Action: S.Finish{value}

law false_reject_scan_reads_value_before_target:
  {T.observe(2n,I.scan_equal(collection(),["yes"],done),schema(),state([entry("a","yes","first"),entry("b","no","skipped"),entry("c","yes","last")]),Nil{}) == S.Prefix{state([entry("a","yes","first"),entry("b","no","skipped"),entry("c","yes","last")]),[S.OperationEvent{D.EnumerateKeys{collection()},S.Reading{D.Keys{["a","b","c"]}}},S.OperationEvent{D.ReadCell{collection(),"a","value"},S.Reading{D.Cell{D.VText{K.encode(["yes"])}}}}]} : S.Trace}
def false_reject_scan_reads_value_before_target(): {==}
