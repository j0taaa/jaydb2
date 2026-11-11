# Deliberately false state/frame/delta claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I

def collection() -> D.Collection: D.Application{"index"}

def entry(key: String,target: String) -> D.Row: I.entry(key,["v"],target)

law false:
  {D.swap_collection(collection(),D.State{[D.Table{"index",Nil{}}],[entry("u","user")]},[entry("n","new")]) == D.State{[D.Table{"index",[entry("n","new")]}],[entry("n","new")]} : D.State}
def false(): {==}
