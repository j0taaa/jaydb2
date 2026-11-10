import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../Controls.bend as X
import ../../../contract/Theorems.bend as G

# A completion returning changed() on refusal must provide this Core clause.
law false:
  G.Publication(S.Response{S.Refusal{}, D.VAbsent{}}, X.seed(), X.changed(), X.changed())
def false(): {==}
