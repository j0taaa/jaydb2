import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Configuration.bend as C
def state() -> D.State:
  D.State{[D.Table{"bills_of_material", []}, D.Table{"bom_components", []}, D.Table{"customers", []}, D.Table{"employees", []}, D.Table{"machines", []}, D.Table{"materials", []}, D.Table{"operations", []}, D.Table{"plants", []}, D.Table{"production_runs", []}, D.Table{"products", []}, D.Table{"purchase_order_lines", []}, D.Table{"purchase_orders", []}, D.Table{"quality_checks", []}, D.Table{"sales_order_lines", []}, D.Table{"sales_orders", []}, D.Table{"stock_lots", []}, D.Table{"supplier_materials", []}, D.Table{"suppliers", []}, D.Table{"units_of_measure", []}, D.Table{"warehouses", []}, D.Table{"work_centers", []}, D.Table{"work_orders", []}], [D.Row{"bench", [
    D.Field{"credential", D.VText{"comparison-token"}},
    D.Field{"id", D.VText{"bench"}}, D.Field{"kind", D.VText{"user"}}]}]}
law initial_valid:
  R.Valid(C.config(), state())
def initial_valid():
  L.Both{{==}, Unit{}}
