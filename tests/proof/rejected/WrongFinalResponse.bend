import Base
import ../../../contract/Requirements.bend as R
import ../../../contract/Semantics.bend as S
import ../../../contract/Data.bend as D
import ../Controls.bend as X
law false:
  {S.Response{S.Success{}, D.VAbsent{}} ==
    R.finalize(S.Response{S.Refusal{}, D.VAbsent{}}, X.configuration(), X.seed()) : S.Response}
def false(): {==}
