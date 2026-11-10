# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Mutation.bend as M

def collection() -> D.Collection: D.Application{"t"}

def row(+key: String,title: String) -> D.Row:
  D.Row{key,[D.Field{"id",D.VText{key}},D.Field{"title",D.VText{title}}]}

def bool_done(b: Bool) -> S.Action: S.Finish{D.VBool{b}}

law false_reject_insert_absent_returns_before_write:
  {M.inserted(collection(),row("k","new"),bool_done,S.Datum{D.Existence{False{}}}) == bool_done(True{}) : S.Action}
def false_reject_insert_absent_returns_before_write(): {==}
