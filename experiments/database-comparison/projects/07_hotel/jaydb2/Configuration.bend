import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Environment.bend as E
def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"amenities", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"property_id", D.TextValue{}, False{}}, D.Column{"unit_price_cents", D.Integer{}, False{}}]},
    D.SchemaTable{"departments", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"monthly_budget_cents", D.Integer{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"property_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"employees", "id", [D.Column{"department_id", D.TextValue{}, False{}}, D.Column{"full_name", D.TextValue{}, False{}}, D.Column{"hourly_rate_cents", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}]},
    D.SchemaTable{"guests", "id", [D.Column{"email", D.TextValue{}, False{}}, D.Column{"full_name", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"loyalty_tier", D.TextValue{}, False{}}]},
    D.SchemaTable{"housekeeping_tasks", "id", [D.Column{"employee_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"planned_minutes", D.Integer{}, False{}}, D.Column{"room_id", D.TextValue{}, False{}}, D.Column{"service_date", D.TextValue{}, False{}}]},
    D.SchemaTable{"maintenance_requests", "id", [D.Column{"description", D.TextValue{}, False{}}, D.Column{"estimated_cost_cents", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"reported_by", D.TextValue{}, False{}}, D.Column{"room_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"payments", "id", [D.Column{"amount_cents", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"method", D.TextValue{}, False{}}, D.Column{"reservation_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"properties", "id", [D.Column{"city", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"timezone", D.TextValue{}, False{}}]},
    D.SchemaTable{"rate_plans", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"nightly_cents", D.Integer{}, False{}}, D.Column{"room_type_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"reservation_amenities", "id", [D.Column{"amenity_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"quantity", D.Integer{}, False{}}, D.Column{"reservation_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"reservation_rates", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"nightly_cents", D.Integer{}, False{}}, D.Column{"rate_plan_id", D.TextValue{}, False{}}, D.Column{"reservation_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"reservations", "id", [D.Column{"check_in", D.TextValue{}, False{}}, D.Column{"guest_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"nights", D.Integer{}, False{}}, D.Column{"room_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"reviews", "id", [D.Column{"comment", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"rating", D.Integer{}, False{}}, D.Column{"reservation_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"room_types", "id", [D.Column{"base_nightly_cents", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"property_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"rooms", "id", [D.Column{"floor", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"room_number", D.TextValue{}, False{}}, D.Column{"room_type_id", D.TextValue{}, False{}}]}]}
def limits() -> S.Limits:
  S.Limits{262144n, 8388608n, 262144n}
def config() -> S.Configuration:
  L.configuration(schema(), limits(), E.identity())
