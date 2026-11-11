# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Index.bend as I
import ../../../library/Key.bend as K
import ../../../library/Query.bend as Q

def collection() -> D.Collection: D.Application{"index"}

def selection_done(selection: Q.Selection) -> S.Action:
  match selection:
    case Q.Selected{record}: S.Finish{record}
    case Q.MissingRow{}: S.Finish{D.VAbsent{}}
    case Q.InvalidFields{}: S.Refuse{D.VAbsent{}}
    case Q.UnexpectedReturn{}: S.Refuse{D.VAbsent{}}

law false:
  {I.lookup(collection(),["x"],selection_done) == S.Access{D.ReadCell{collection(),K.encode(["x"]),"value"},r => S.Finish{D.VAbsent{}}} : S.Action}
def false(): {==}
