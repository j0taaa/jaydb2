# Deliberately false state/frame/delta claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I

def collection() -> D.Collection: D.Application{"index"}

def entry(key: String,target: String) -> D.Row: I.entry(key,["v"],target)

law false:
  {D.rows_collection(collection(),D.swap_collection(collection(),D.State{Nil{},Nil{}},[entry("n","new")])) == Some{[entry("n","new")]} : Maybe<&2,List<&2,D.Row>>}
def false(): {==}
