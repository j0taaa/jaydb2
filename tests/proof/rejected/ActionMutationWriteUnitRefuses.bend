# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Action.bend as A

law false:
  {A.written(S.Finish{D.VAbsent{}},S.UnitValue{}) == S.Refuse{D.VText{"unexpected write return"}} : S.Action}
def false(): {==}
