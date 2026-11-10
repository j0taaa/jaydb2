# Deliberately false actual voucher behavior; must reject at the proof body.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Semantics.bend as S
import ../../../../contract/Requirements.bend as R
import ../VoucherPairProofs.bend as P

def columns() -> List<&2,D.Column>: [D.Column{"enabled",D.Boolean{},True{}},D.Column{"id",D.TextValue{},False{}},D.Column{"input",D.TextValue{},True{}},D.Column{"operation",D.TextValue{},True{}},D.Column{"owner",D.TextValue{},False{}},D.Column{"result",D.TextValue{},True{}}]

def schema() -> D.Schema: D.Schema{[D.SchemaTable{"alice","id",columns()}]}

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"alice",rows}],Nil{}}

def working(cancel: Bool) -> D.State: P.state("alice",state(Nil{}),Nil{},"q","tea",cancel)

def configuration() -> S.Configuration: S.Configuration{schema(),S.NoneLaw{},S.Limits{1000n,1000n,1000n},""}

law false_reject_voucher_cancellation_publishes_working_pair:
  {S.publish(R.finalize(S.Response{S.Refusal{},D.VText{"cancelled"}},configuration(),working(True{})),state(Nil{}),working(True{})) == working(True{}) : D.State}
def false_reject_voucher_cancellation_publishes_working_pair(): {==}
