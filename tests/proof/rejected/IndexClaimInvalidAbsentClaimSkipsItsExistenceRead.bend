# Deliberately false input-content claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Index.bend as I
import ../../../src/Termination.bend as T
import ../../../library/IndexEntryProofs.bend as Entry

def collection() -> D.Collection: D.Application{"index"}

def schema() -> D.Schema: D.Schema{[Entry.schema("index")]}

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"index",rows}],Nil{}}

def bool_done(value: Bool) -> S.Action: S.Finish{D.VBool{value}}

def badkey() -> String: SCon{Chr{55296},SNil{}}

law false:
  {T.observe(3n,I.claim(collection(),["v"],badkey(),bool_done),schema(),state(Nil{}),Nil{}) == S.Final{state(Nil{}),Nil{},S.Response{S.DataError{},D.VAbsent{}}} : S.Trace}
def false(): {==}
