# Deliberately false actual voucher behavior; must reject at the proof body.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Semantics.bend as S
import ../../Voucher.bend as V
import ../VoucherPairProofs.bend as P
import ../../../../src/Termination.bend as T
import ../../../../library/ReceiptLookupProofs.bend as Binding

def columns() -> List<&2,D.Column>: [D.Column{"enabled",D.Boolean{},True{}},D.Column{"id",D.TextValue{},False{}},D.Column{"input",D.TextValue{},True{}},D.Column{"operation",D.TextValue{},True{}},D.Column{"owner",D.TextValue{},False{}},D.Column{"result",D.TextValue{},True{}}]

def schema() -> D.Schema: D.Schema{[D.SchemaTable{"alice","id",columns()}]}

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"alice",rows}],Nil{}}

def working(cancel: Bool) -> D.State: P.state("alice",state(Nil{}),Nil{},"q","tea",cancel)

def hit_events() -> List<&2,S.OperationEvent>: Binding.hit_events("alice",V.receipt("q"),V.canonical("tea",False{}),V.operation(),D.VText{V.voucher("q")})

law false_reject_voucher_repeat_writes_again:
  {T.observe(6n,V.command("alice",V.Issue{"q","tea",False{}}),schema(),working(False{}),Nil{}) == S.Final{working(False{}),P.events("alice","q","tea",False{},hit_events()),S.Response{S.Success{},D.VText{V.voucher("q")}}} : S.Trace}
def false_reject_voucher_repeat_writes_again(): {==}
