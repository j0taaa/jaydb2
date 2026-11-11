# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Mutation.bend as M

def collection() -> D.Collection: D.Application{"t"}

def row(+key: String,title: String) -> D.Row:
  D.Row{key,[D.Field{"id",D.VText{key}},D.Field{"title",D.VText{title}}]}

def bool_done(b: Bool) -> S.Action: S.Finish{D.VBool{b}}

def accept_absent(obs: D.Observation) -> Bool:
  match obs:
    case D.RowAbsent{}: True{}
    case D.Cell{value}: False{}
    case D.Keys{keys}: False{}
    case D.Count{count}: False{}
    case D.Existence{exists}: False{}

law false:
  {M.replace_received(~accept_absent,collection(),row("k","new"),bool_done,S.Datum{D.RowAbsent{}}) == bool_done(False{}) : S.Action}
def false(): {==}
