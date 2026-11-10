# Deliberately false actual protocol/certificate claim; reject at proof body.
import Base
import ../../../../contract/Data.bend as D
import ../../Voucher.bend as V
import ../../Initial.bend as Initial
import ../VoucherPairProofs.bend as P

def columns() -> List<&2,D.Column>: [D.Column{"enabled",D.Boolean{},True{}},D.Column{"id",D.TextValue{},False{}},D.Column{"input",D.TextValue{},True{}},D.Column{"operation",D.TextValue{},True{}},D.Column{"owner",D.TextValue{},False{}},D.Column{"result",D.TextValue{},True{}}]

def table(name: String) -> D.SchemaTable: D.SchemaTable{name,"id",columns()}

def schema() -> D.Schema: D.Schema{[table("alice"),table("bob")]}

def seed() -> D.State: D.State{Initial.tables(),Nil{}}

def created() -> D.State: P.state("alice",seed(),[Initial.gate("alice")],"q","tea",False{})

law false_reject_actual_delete_pretends_its_nonempty_state_is_unchanged:
  {D.operate(schema(),created(),D.RemoveRow{D.Application{"alice"},V.receipt("q")}) == D.Changed{created()} : D.ResultOp}
def false_reject_actual_delete_pretends_its_nonempty_state_is_unchanged(): {==}
