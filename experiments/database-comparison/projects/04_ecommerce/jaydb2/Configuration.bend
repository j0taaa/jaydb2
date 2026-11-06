import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Environment.bend as E
def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"categories", "id", [D.Column{"department", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]},
    D.SchemaTable{"customers", "id", [D.Column{"country_code", D.TextValue{}, False{}}, D.Column{"email", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]},
    D.SchemaTable{"inventory", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"product_id", D.TextValue{}, False{}}, D.Column{"quantity", D.Integer{}, False{}}, D.Column{"reorder_level", D.Integer{}, False{}}, D.Column{"warehouse_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"order_items", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"order_id", D.TextValue{}, False{}}, D.Column{"product_id", D.TextValue{}, False{}}, D.Column{"quantity", D.Integer{}, False{}}, D.Column{"unit_price_cents", D.Integer{}, False{}}]},
    D.SchemaTable{"orders", "id", [D.Column{"customer_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"ordered_at", D.TextValue{}, False{}}, D.Column{"status", D.TextValue{}, False{}}, D.Column{"total_cents", D.Integer{}, False{}}]},
    D.SchemaTable{"payments", "id", [D.Column{"amount_cents", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"method", D.TextValue{}, False{}}, D.Column{"order_id", D.TextValue{}, False{}}, D.Column{"status", D.TextValue{}, False{}}]},
    D.SchemaTable{"products", "id", [D.Column{"active", D.Boolean{}, False{}}, D.Column{"category_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"price_cents", D.Integer{}, False{}}]},
    D.SchemaTable{"warehouses", "id", [D.Column{"active", D.Boolean{}, False{}}, D.Column{"city", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]}]}
def limits() -> S.Limits:
  S.Limits{262144n, 8388608n, 262144n}
def config() -> S.Configuration:
  L.configuration(schema(), limits(), E.identity())
