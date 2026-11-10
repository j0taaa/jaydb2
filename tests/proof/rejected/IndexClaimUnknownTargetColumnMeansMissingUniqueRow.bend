# Deliberately false input-content claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Index.bend as I
import ../../../library/Key.bend as K
import ../../../library/Query.bend as Q
import ../../../src/Termination.bend as T

def collection() -> D.Collection: D.Application{"index"}

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"index",rows}],Nil{}}

def selection_done(result: Q.Selection) -> S.Action:
  match result:
    case Q.Selected{record}: S.Finish{record}
    case Q.MissingRow{}: S.Finish{D.VAbsent{}}
    case _: S.Refuse{D.VAbsent{}}

def no_target() -> D.Schema: D.Schema{[D.SchemaTable{"index","id",[D.Column{"id",D.TextValue{},False{}}]}]}

law false_reject_unknown_target_column_means_missing_unique_row:
  {T.observe(2n,I.lookup(collection(),["v"],selection_done),no_target(),state(Nil{}),Nil{}) == S.Final{state(Nil{}),[S.OperationEvent{D.ReadCell{collection(),K.encode(["v"]),"target"},S.Reading{D.RowAbsent{}}}],S.Response{S.Success{},D.VAbsent{}}} : S.Trace}
def false_reject_unknown_target_column_means_missing_unique_row(): {==}
