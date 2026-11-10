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

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"index",rows}],Nil{}}

def maybe_done(value: Maybe<&2,D.Value>) -> S.Action:
  match value:
    case None{}: S.Finish{D.VAbsent{}}
    case Some{value}: S.Finish{value}

law false_reject_visit_missing_skips_second_read:
  {T.observe(3n,I.visit(I.Scan{collection(),K.encode(["yes"])},"missing",maybe_done),schema(),state(Nil{}),Nil{}) == S.Final{state(Nil{}),[S.OperationEvent{D.ReadCell{collection(),"missing","target"},S.Reading{D.RowAbsent{}}}],S.Response{S.Success{},D.VAbsent{}}} : S.Trace}
def false_reject_visit_missing_skips_second_read(): {==}
