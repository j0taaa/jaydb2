import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Environment.bend as E
def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"addresses", "id", [D.Column{"district_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"number", D.Integer{}, False{}}, D.Column{"street", D.TextValue{}, False{}}]},
    D.SchemaTable{"assets", "id", [D.Column{"address_id", D.TextValue{}, False{}}, D.Column{"department_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"replacement_cost_cents", D.Integer{}, False{}}]},
    D.SchemaTable{"budget_accounts", "id", [D.Column{"account_code", D.TextValue{}, False{}}, D.Column{"allocated_cents", D.Integer{}, False{}}, D.Column{"department_id", D.TextValue{}, False{}}, D.Column{"fiscal_year", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}]},
    D.SchemaTable{"contracts", "id", [D.Column{"ceiling_cents", D.Integer{}, False{}}, D.Column{"department_id", D.TextValue{}, False{}}, D.Column{"description", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"vendor_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"departments", "id", [D.Column{"annual_budget_cents", D.Integer{}, False{}}, D.Column{"district_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]},
    D.SchemaTable{"districts", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"population", D.Integer{}, False{}}]},
    D.SchemaTable{"expenditures", "id", [D.Column{"amount_cents", D.Integer{}, False{}}, D.Column{"budget_account_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"posted_date", D.TextValue{}, False{}}, D.Column{"work_order_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"fee_invoices", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"issued_date", D.TextValue{}, False{}}, D.Column{"permit_id", D.TextValue{}, False{}}, D.Column{"resident_id", D.TextValue{}, False{}}, D.Column{"total_cents", D.Integer{}, False{}}]},
    D.SchemaTable{"fee_payments", "id", [D.Column{"amount_cents", D.Integer{}, False{}}, D.Column{"fee_invoice_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"method", D.TextValue{}, False{}}, D.Column{"received_date", D.TextValue{}, False{}}]},
    D.SchemaTable{"inspection_types", "id", [D.Column{"checklist_items", D.Integer{}, False{}}, D.Column{"department_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]},
    D.SchemaTable{"inspections", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"inspection_date", D.TextValue{}, False{}}, D.Column{"inspection_type_id", D.TextValue{}, False{}}, D.Column{"inspector_id", D.TextValue{}, False{}}, D.Column{"property_id", D.TextValue{}, False{}}, D.Column{"result", D.TextValue{}, False{}}]},
    D.SchemaTable{"material_catalog", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"unit", D.TextValue{}, False{}}, D.Column{"unit_cost_cents", D.Integer{}, False{}}]},
    D.SchemaTable{"permit_applications", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"permit_type_id", D.TextValue{}, False{}}, D.Column{"property_id", D.TextValue{}, False{}}, D.Column{"resident_id", D.TextValue{}, False{}}, D.Column{"submitted_date", D.TextValue{}, False{}}]},
    D.SchemaTable{"permit_types", "id", [D.Column{"base_fee_cents", D.Integer{}, False{}}, D.Column{"department_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]},
    D.SchemaTable{"permits", "id", [D.Column{"application_id", D.TextValue{}, False{}}, D.Column{"approved_by", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"issued_date", D.TextValue{}, False{}}, D.Column{"valid_days", D.Integer{}, False{}}]},
    D.SchemaTable{"properties", "id", [D.Column{"address_id", D.TextValue{}, False{}}, D.Column{"assessed_value_cents", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"owner_id", D.TextValue{}, False{}}, D.Column{"property_kind", D.TextValue{}, False{}}]},
    D.SchemaTable{"request_updates", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"message", D.TextValue{}, False{}}, D.Column{"request_id", D.TextValue{}, False{}}, D.Column{"staff_id", D.TextValue{}, False{}}, D.Column{"update_date", D.TextValue{}, False{}}]},
    D.SchemaTable{"residents", "id", [D.Column{"birth_year", D.Integer{}, False{}}, D.Column{"district_id", D.TextValue{}, False{}}, D.Column{"full_name", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}]},
    D.SchemaTable{"service_categories", "id", [D.Column{"department_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"target_days", D.Integer{}, False{}}]},
    D.SchemaTable{"service_requests", "id", [D.Column{"category_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"opened_date", D.TextValue{}, False{}}, D.Column{"property_id", D.TextValue{}, False{}}, D.Column{"resident_id", D.TextValue{}, False{}}, D.Column{"status", D.TextValue{}, False{}}]},
    D.SchemaTable{"staff", "id", [D.Column{"department_id", D.TextValue{}, False{}}, D.Column{"full_name", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"role", D.TextValue{}, False{}}]},
    D.SchemaTable{"vendors", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"registration", D.TextValue{}, False{}}]},
    D.SchemaTable{"violations", "id", [D.Column{"code", D.TextValue{}, False{}}, D.Column{"fine_cents", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"inspection_id", D.TextValue{}, False{}}, D.Column{"status", D.TextValue{}, False{}}]},
    D.SchemaTable{"work_order_assignments", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"planned_hours", D.Integer{}, False{}}, D.Column{"staff_id", D.TextValue{}, False{}}, D.Column{"work_order_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"work_order_materials", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"material_id", D.TextValue{}, False{}}, D.Column{"quantity", D.Integer{}, False{}}, D.Column{"work_order_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"work_orders", "id", [D.Column{"asset_id", D.TextValue{}, False{}}, D.Column{"contract_id", D.TextValue{}, False{}}, D.Column{"estimated_cost_cents", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"request_id", D.TextValue{}, False{}}, D.Column{"scheduled_date", D.TextValue{}, False{}}]}]}
def limits() -> S.Limits:
  S.Limits{262144n, 8388608n, 262144n}
def config() -> S.Configuration:
  L.configuration(schema(), limits(), E.identity())
