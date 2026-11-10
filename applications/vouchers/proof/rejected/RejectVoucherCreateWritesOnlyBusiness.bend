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

law false_reject_voucher_create_writes_only_business:
  {T.observe(3n,V.create("alice","q","tea",False{}),schema(),state(Nil{}),Nil{}) == S.Final{state([P.voucher_row("alice","q","tea")]),[S.OperationEvent{P.voucher_op("alice","q","tea"),S.Write{}}],S.Response{S.Success{},D.VText{V.voucher("q")}}} : S.Trace}
def false_reject_voucher_create_writes_only_business(): {==}
