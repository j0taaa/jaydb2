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

law false:
  {T.observe(2n,I.lookup(collection(),["v"],selection_done),schema(),state([I.unique(["earlier"],"wrong"),I.unique(["v"],"right")]),Nil{}) == S.Final{state([I.unique(["earlier"],"wrong"),I.unique(["v"],"right")]),[S.OperationEvent{D.ReadCell{collection(),K.encode(["v"]),"target"},S.Reading{D.Cell{D.VText{"right"}}}}],S.Response{S.Success{},D.VRecord{"target",D.VText{"wrong"},D.VRecordEmpty{}}}} : S.Trace}
def false(): {==}
