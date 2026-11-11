# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Index.bend as I
import ../../../library/Query.bend as Q

def maybe_done(value: Maybe<&2,D.Value>) -> S.Action:
  match value:
    case None{}: S.Finish{D.VAbsent{}}
    case Some{value}: S.Finish{value}

law false:
  {I.selected("v",maybe_done,Q.InvalidFields{}) == maybe_done(None{}) : S.Action}
def false(): {==}
