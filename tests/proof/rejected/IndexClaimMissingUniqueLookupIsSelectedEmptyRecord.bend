# Deliberately false input-content claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Index.bend as I
import ../../../library/Key.bend as K
import ../../../library/Query.bend as Q
import ../../../src/Termination.bend as T
import ../../../library/IndexEntryProofs.bend as Entry

def collection() -> D.Collection: D.Application{"index"}

def schema() -> D.Schema: D.Schema{[Entry.schema("index")]}

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"index",rows}],Nil{}}

def selection_done(result: Q.Selection) -> S.Action:
  match result:
    case Q.Selected{record}: S.Finish{record}
    case Q.MissingRow{}: S.Finish{D.VAbsent{}}
    case _: S.Refuse{D.VAbsent{}}

law false_reject_missing_unique_lookup_is_selected_empty_record:
  {T.observe(2n,I.lookup(collection(),["v"],selection_done),schema(),state(Nil{}),Nil{}) == S.Final{state(Nil{}),[S.OperationEvent{D.ReadCell{collection(),K.encode(["v"]),"target"},S.Reading{D.RowAbsent{}}}],S.Response{S.Success{},D.VRecordEmpty{}}} : S.Trace}
def false_reject_missing_unique_lookup_is_selected_empty_record(): {==}
