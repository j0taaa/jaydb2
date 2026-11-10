import Base
import ../../../contract/Data.bend as D
import ../../../contract/Logic.bend as L
import ../../../contract/Requirements.bend as R
import ../Controls.bend as X
law false:
  R.Valid(X.configuration(), D.State{[D.Table{"unexpected", Nil{}}], Nil{}})
def false(): L.Both{{==}, Unit{}}
