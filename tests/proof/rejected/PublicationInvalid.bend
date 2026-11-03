import Base
import ../../../contract/Requirements.bend as R
import ../../../contract/Logic.bend as L
import ../Certificate.bend as T
import ../Preparation.bend as P

law false:
  R.Valid(T.configuration(), P.duplicated())
def false():
  L.Both{{==}, L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, Unit{}}}}}
