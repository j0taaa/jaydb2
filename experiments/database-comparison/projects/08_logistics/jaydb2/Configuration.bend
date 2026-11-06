import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Environment.bend as E
def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"addresses", "id", [D.Column{"customer_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"label", D.TextValue{}, False{}}, D.Column{"postal_code", D.TextValue{}, False{}}]},
    D.SchemaTable{"carriers", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"service_level", D.TextValue{}, False{}}]},
    D.SchemaTable{"customers", "id", [D.Column{"billing_email", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]},
    D.SchemaTable{"delivery_attempts", "id", [D.Column{"attempt_date", D.TextValue{}, False{}}, D.Column{"driver_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"shipment_id", D.TextValue{}, False{}}, D.Column{"successful", D.Boolean{}, False{}}]},
    D.SchemaTable{"drivers", "id", [D.Column{"full_name", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"license_class", D.TextValue{}, False{}}]},
    D.SchemaTable{"inventory", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"product_id", D.TextValue{}, False{}}, D.Column{"quantity", D.Integer{}, False{}}, D.Column{"warehouse_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"invoice_lines", "id", [D.Column{"charge_cents", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"invoice_id", D.TextValue{}, False{}}, D.Column{"shipment_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"invoices", "id", [D.Column{"customer_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"issued_date", D.TextValue{}, False{}}, D.Column{"total_cents", D.Integer{}, False{}}]},
    D.SchemaTable{"products", "id", [D.Column{"customer_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"sku", D.TextValue{}, False{}}, D.Column{"unit_weight_grams", D.Integer{}, False{}}]},
    D.SchemaTable{"routes", "id", [D.Column{"carrier_id", D.TextValue{}, False{}}, D.Column{"destination_warehouse_id", D.TextValue{}, False{}}, D.Column{"distance_km", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"origin_warehouse_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"shipment_items", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"product_id", D.TextValue{}, False{}}, D.Column{"quantity", D.Integer{}, False{}}, D.Column{"shipment_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"shipment_legs", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"sequence", D.Integer{}, False{}}, D.Column{"shipment_id", D.TextValue{}, False{}}, D.Column{"trip_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"shipments", "id", [D.Column{"carrier_id", D.TextValue{}, False{}}, D.Column{"customer_id", D.TextValue{}, False{}}, D.Column{"destination_address_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"origin_warehouse_id", D.TextValue{}, False{}}, D.Column{"service", D.TextValue{}, False{}}]},
    D.SchemaTable{"tracking_events", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"occurred_at", D.TextValue{}, False{}}, D.Column{"shipment_id", D.TextValue{}, False{}}, D.Column{"status", D.TextValue{}, False{}}]},
    D.SchemaTable{"trips", "id", [D.Column{"departure_date", D.TextValue{}, False{}}, D.Column{"driver_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"route_id", D.TextValue{}, False{}}, D.Column{"vehicle_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"vehicle_types", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"max_payload_kg", D.Integer{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]},
    D.SchemaTable{"vehicles", "id", [D.Column{"carrier_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"payload_kg", D.Integer{}, False{}}, D.Column{"registration", D.TextValue{}, False{}}, D.Column{"vehicle_type_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"warehouses", "id", [D.Column{"capacity_pallets", D.Integer{}, False{}}, D.Column{"city", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]}]}
def limits() -> S.Limits:
  S.Limits{262144n, 8388608n, 262144n}
def config() -> S.Configuration:
  L.configuration(schema(), limits(), E.identity())
