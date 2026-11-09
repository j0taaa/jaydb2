import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Configuration.bend as C
def state() -> D.State:
  D.State{[D.Table{"addresses", []}, D.Table{"assets", []}, D.Table{"budget_accounts", []}, D.Table{"contracts", []}, D.Table{"departments", []}, D.Table{"districts", []}, D.Table{"expenditures", []}, D.Table{"fee_invoices", []}, D.Table{"fee_payments", []}, D.Table{"inspection_types", []}, D.Table{"inspections", []}, D.Table{"material_catalog", []}, D.Table{"permit_applications", []}, D.Table{"permit_types", []}, D.Table{"permits", []}, D.Table{"properties", []}, D.Table{"request_updates", []}, D.Table{"residents", []}, D.Table{"service_categories", []}, D.Table{"service_requests", []}, D.Table{"staff", []}, D.Table{"vendors", []}, D.Table{"violations", []}, D.Table{"work_order_assignments", []}, D.Table{"work_order_materials", []}, D.Table{"work_orders", []}], [D.Row{"bench", [
    D.Field{"credential", D.VText{"comparison-token"}},
    D.Field{"id", D.VText{"bench"}}, D.Field{"kind", D.VText{"user"}}]}]}
law initial_valid:
  R.Valid(C.config(), state())
def initial_valid():
  L.Both{{==}, Unit{}}
