import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Configuration.bend as C
def state() -> D.State:
  D.State{[D.Table{"addresses", []}, D.Table{"carriers", []}, D.Table{"customers", []}, D.Table{"delivery_attempts", []}, D.Table{"drivers", []}, D.Table{"inventory", []}, D.Table{"invoice_lines", []}, D.Table{"invoices", []}, D.Table{"products", []}, D.Table{"routes", []}, D.Table{"shipment_items", []}, D.Table{"shipment_legs", []}, D.Table{"shipments", []}, D.Table{"tracking_events", []}, D.Table{"trips", []}, D.Table{"vehicle_types", []}, D.Table{"vehicles", []}, D.Table{"warehouses", []}], [D.Row{"bench", [
    D.Field{"credential", D.VText{"comparison-token"}},
    D.Field{"id", D.VText{"bench"}}, D.Field{"kind", D.VText{"user"}}]}]}
law initial_valid:
  R.Valid(C.config(), state())
def initial_valid():
  L.Both{{==}, Unit{}}
