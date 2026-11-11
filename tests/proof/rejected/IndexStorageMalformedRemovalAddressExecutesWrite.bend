# Deliberately false state/frame/delta claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Index.bend as I
import ../../../library/IndexEntryProofs.bend as Entry
import ../../../library/MutationWritePlan.bend as Plan

def collection() -> D.Collection: D.Application{"index"}

def base() -> D.Collection: D.Application{"base"}

def schema() -> D.Schema: D.Schema{[Entry.schema("base"),Entry.schema("index")]}

def entry(key: String,target: String) -> D.Row: I.entry(key,["v"],target)

def state(index: List<&2,D.Row>,rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"base",rows},D.Table{"index",index}],Nil{}}

def badkey() -> String: SCon{Chr{55296},SNil{}}

law false:
  {Plan.plan([D.RemoveRow{collection(),badkey()}],schema(),state([entry("a","old")],Nil{})) == Plan.WriteHandoff{state([entry("a","old")],Nil{}),[S.OperationEvent{D.RemoveRow{collection(),badkey()},S.Write{}}]} : Plan.Plan}
def false(): {==}
