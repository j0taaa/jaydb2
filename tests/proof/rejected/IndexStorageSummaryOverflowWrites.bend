# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Summary.bend as Summary

def collection() -> D.Collection: D.Application{"index"}

law false:
  {Summary.store_result(collection(),"s",None{},S.Finish{D.VAbsent{}}) == S.Finish{D.VAbsent{}} : S.Action}
def false(): {==}
