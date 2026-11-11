import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Int64DivisionProofs.bend as P
import ../../../library/Int64DivisionSpec.bend as S

law false:
  S.DivisionCorrect(V.Int64{0,7},V.Int64{0,3},Some{I.Division{V.Int64{0,3},V.Int64{0,0}}})
def false():
  S.Meaning{{==},{==},{==},{==},{==},{==}}
