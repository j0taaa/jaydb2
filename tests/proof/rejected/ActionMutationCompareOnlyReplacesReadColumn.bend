# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Action.bend as A
import ../../../library/Mutation.bend as M

def collection() -> D.Collection: D.Application{"t"}

def row(+key: String,title: String) -> D.Row:
  D.Row{key,[D.Field{"id",D.VText{key}},D.Field{"title",D.VText{title}}]}

def bool_done(b: Bool) -> S.Action: S.Finish{D.VBool{b}}

law false:
  {M.cas_received(collection(),row("k","new"),D.VText{"k"},bool_done,S.Datum{D.Cell{D.VText{"k"}}}) == S.Access{D.DefineColumn{collection(),"k","id",D.VText{"k"}},r => A.written(bool_done(True{}),r)} : S.Action}
def false(): {==}
