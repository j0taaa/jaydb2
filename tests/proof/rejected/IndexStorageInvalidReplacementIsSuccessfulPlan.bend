# Deliberately false state/frame/delta claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/IndexEntryProofs.bend as Entry
import ../../../library/MutationWritePlan.bend as Plan

def collection() -> D.Collection: D.Application{"index"}

def base() -> D.Collection: D.Application{"base"}

def schema() -> D.Schema: D.Schema{[Entry.schema("base"),Entry.schema("index")]}

def state(index: List<&2,D.Row>,rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"base",rows},D.Table{"index",index}],Nil{}}

def badrow() -> D.Row: D.Row{"n",Nil{}}

law false:
  {Plan.plan([D.DefineRow{collection(),"n",Nil{}}],schema(),state(Nil{},Nil{})) == Plan.WriteHandoff{state([badrow()],Nil{}),[S.OperationEvent{D.DefineRow{collection(),"n",Nil{}},S.Write{}}]} : Plan.Plan}
def false(): {==}
