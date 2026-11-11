# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Index.bend as I

def maybe_done(value: Maybe<&2,D.Value>) -> S.Action:
  match value:
    case None{}: S.Finish{D.VAbsent{}}
    case Some{value}: S.Finish{value}

law false:
  {I.projected("wanted",maybe_done,I.Target{"target","other"}) == maybe_done(Some{D.VText{"target"}}) : S.Action}
def false(): {==}
