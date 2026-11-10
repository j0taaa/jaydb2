import Base
import ../../../contract/Theorems.bend as G
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../Controls.bend as X
import ../WrongSteps.bend as Wrong
import ../Instances.bend as I

# A run step that feeds a changed root after the program refused.
law false:
  G.Step<X.configuration(), X.seed(), X.request(), Wrong.accept, X.changed()>
def false():
  G.StepRan{X.context(), X.program(), 1n, X.seed(), Nil{}, S.Response{S.Refusal{}, D.VAbsent{}},
    I.refused(), I.refused_bytes(), {==}, {==}, {==}, {==}}
