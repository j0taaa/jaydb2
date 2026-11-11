# Deliberately false state/frame/delta claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I
import ../../../library/IndexMaintenancePlan.bend as Maint
import ../../../library/TableLaws.bend as Table

def collection() -> D.Collection: D.Application{"index"}

def base() -> D.Collection: D.Application{"base"}

def entry(key: String,target: String) -> D.Row: I.entry(key,["v"],target)

def state(index: List<&2,D.Row>,rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"base",rows},D.Table{"index",index}],Nil{}}

def identity(rows: List<&2,D.Row>) -> List<&2,D.Row>: rows

law false:
  Table.ExactIndex(~identity,base(),collection(),Maint.state(collection(),state([entry("a","stale")],[entry("b","business")]),Nil{},[entry("n","new")],[entry("a","stale")]))
def false(): {==}
