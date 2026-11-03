import Base
import ../../../contract/Semantics.bend as S
import ../../../contract/Logic.bend as L
import ../Certificate.bend as T

law false:
  S.Satisfies(T.configuration(), S.Executing{T.initial(), T.context(), T.code(), T.arguments(), T.initial(), Nil{}})
def false():
  L.Both{{==}, L.Both{L.Left{{==}}, Unit{}}}
