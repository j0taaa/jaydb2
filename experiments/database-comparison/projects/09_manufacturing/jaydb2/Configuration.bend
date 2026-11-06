import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Environment.bend as E
def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"bills_of_material", "id", [D.Column{"active", D.Boolean{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"product_id", D.TextValue{}, False{}}, D.Column{"revision", D.TextValue{}, False{}}]},
    D.SchemaTable{"bom_components", "id", [D.Column{"bill_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"material_id", D.TextValue{}, False{}}, D.Column{"quantity", D.Integer{}, False{}}]},
    D.SchemaTable{"customers", "id", [D.Column{"credit_limit_cents", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]},
    D.SchemaTable{"employees", "id", [D.Column{"full_name", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"plant_id", D.TextValue{}, False{}}, D.Column{"role", D.TextValue{}, False{}}]},
    D.SchemaTable{"machines", "id", [D.Column{"asset_tag", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"service_interval_hours", D.Integer{}, False{}}, D.Column{"work_center_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"materials", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"reorder_quantity", D.Integer{}, False{}}, D.Column{"sku", D.TextValue{}, False{}}, D.Column{"unit_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"operations", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"machine_id", D.TextValue{}, False{}}, D.Column{"planned_minutes", D.Integer{}, False{}}, D.Column{"sequence", D.Integer{}, False{}}, D.Column{"work_order_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"plants", "id", [D.Column{"city", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]},
    D.SchemaTable{"production_runs", "id", [D.Column{"completed_quantity", D.Integer{}, False{}}, D.Column{"employee_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"operation_id", D.TextValue{}, False{}}, D.Column{"scrap_quantity", D.Integer{}, False{}}]},
    D.SchemaTable{"products", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"list_price_cents", D.Integer{}, False{}}, D.Column{"sku", D.TextValue{}, False{}}, D.Column{"unit_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"purchase_order_lines", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"material_id", D.TextValue{}, False{}}, D.Column{"purchase_order_id", D.TextValue{}, False{}}, D.Column{"quantity", D.Integer{}, False{}}, D.Column{"unit_cost_cents", D.Integer{}, False{}}]},
    D.SchemaTable{"purchase_orders", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"ordered_date", D.TextValue{}, False{}}, D.Column{"supplier_id", D.TextValue{}, False{}}, D.Column{"total_cents", D.Integer{}, False{}}, D.Column{"warehouse_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"quality_checks", "id", [D.Column{"defect_count", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"inspector_id", D.TextValue{}, False{}}, D.Column{"production_run_id", D.TextValue{}, False{}}, D.Column{"result", D.TextValue{}, False{}}]},
    D.SchemaTable{"sales_order_lines", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"product_id", D.TextValue{}, False{}}, D.Column{"quantity", D.Integer{}, False{}}, D.Column{"sales_order_id", D.TextValue{}, False{}}, D.Column{"unit_price_cents", D.Integer{}, False{}}]},
    D.SchemaTable{"sales_orders", "id", [D.Column{"customer_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"ordered_date", D.TextValue{}, False{}}, D.Column{"status", D.TextValue{}, False{}}, D.Column{"total_cents", D.Integer{}, False{}}]},
    D.SchemaTable{"stock_lots", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"material_id", D.TextValue{}, False{}}, D.Column{"quantity", D.Integer{}, False{}}, D.Column{"supplier_id", D.TextValue{}, False{}}, D.Column{"warehouse_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"supplier_materials", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"material_id", D.TextValue{}, False{}}, D.Column{"supplier_id", D.TextValue{}, False{}}, D.Column{"unit_cost_cents", D.Integer{}, False{}}]},
    D.SchemaTable{"suppliers", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"lead_days", D.Integer{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]},
    D.SchemaTable{"units_of_measure", "id", [D.Column{"code", D.TextValue{}, False{}}, D.Column{"description", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}]},
    D.SchemaTable{"warehouses", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"plant_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"work_centers", "id", [D.Column{"hourly_cost_cents", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"plant_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"work_orders", "id", [D.Column{"due_date", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"planned_quantity", D.Integer{}, False{}}, D.Column{"product_id", D.TextValue{}, False{}}, D.Column{"work_center_id", D.TextValue{}, False{}}]}]}
def limits() -> S.Limits:
  S.Limits{262144n, 8388608n, 262144n}
def config() -> S.Configuration:
  L.configuration(schema(), limits(), E.identity())
