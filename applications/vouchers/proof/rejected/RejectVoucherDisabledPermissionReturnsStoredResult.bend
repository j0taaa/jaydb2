# Deliberately false actual voucher behavior; must reject at the proof body.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Semantics.bend as S
import ../../Voucher.bend as V
import ../VoucherPairProofs.bend as P
import ../../../../src/Termination.bend as T

def columns() -> List<&2,D.Column>: [D.Column{"enabled",D.Boolean{},True{}},D.Column{"id",D.TextValue{},False{}},D.Column{"input",D.TextValue{},True{}},D.Column{"operation",D.TextValue{},True{}},D.Column{"owner",D.TextValue{},False{}},D.Column{"result",D.TextValue{},True{}}]

def schema() -> D.Schema: D.Schema{[D.SchemaTable{"alice","id",columns()}]}

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"alice",rows}],Nil{}}

def permission(enabled: Bool) -> D.Row: D.Row{"permission",[D.Field{"enabled",D.VBool{enabled}},D.Field{"id",D.VText{"permission"}},D.Field{"input",D.VAbsent{}},D.Field{"operation",D.VAbsent{}},D.Field{"owner",D.VText{"alice"}},D.Field{"result",D.VAbsent{}}]}

def disabled() -> D.State: P.state("alice",state([permission(False{})]),[permission(False{})],"q","tea",False{})

law false_reject_voucher_disabled_permission_returns_stored_result:
  {T.observe(5n,V.dispatch("alice",V.Issue{"q","tea",False{}}),schema(),disabled(),Nil{}) == S.Final{disabled(),[S.OperationEvent{D.ReadCell{D.Application{"alice"},"permission","enabled"},S.Reading{D.Cell{D.VBool{False{}}}}}],S.Response{S.Success{},D.VText{V.voucher("q")}}} : S.Trace}
def false_reject_voucher_disabled_permission_returns_stored_result(): {==}
