import Base
import ../../../library/Value.bend as V
import ../../../library/Int64DivisionSpec.bend as Division
import ../../../library/AggregateModel.bend as M
import ../../../library/AggregateAverageSpec.bend as Average

law false_negative_meaning_accepts_an_inexact_quotient:
  Average.Meaning<[V.Int64{0,1},V.Int64{0,2}],V.Int64{0,2}>
def false_negative_meaning_accepts_an_inexact_quotient():
  Average.Meaning{V.Int64{0,3},V.Int64{0,2},V.Int64{0,0},{==},{==},
    M.Both{M.Representable{V.Int64{0,3},{==}},M.Both{M.Representable{V.Int64{0,2},{==}},Unit{}}},
    Division.Meaning{{==},{==},{==},{==},{==},{==}}}
