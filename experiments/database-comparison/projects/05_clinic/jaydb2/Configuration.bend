import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Environment.bend as E
def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"appointments", "id", [D.Column{"clinician_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"patient_id", D.TextValue{}, False{}}, D.Column{"room_id", D.TextValue{}, False{}}, D.Column{"starts_at", D.TextValue{}, False{}}, D.Column{"status", D.TextValue{}, False{}}]},
    D.SchemaTable{"clinicians", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"license_code", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"specialty_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"diagnoses", "id", [D.Column{"code", D.TextValue{}, False{}}, D.Column{"description", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}]},
    D.SchemaTable{"encounter_diagnoses", "id", [D.Column{"diagnosis_id", D.TextValue{}, False{}}, D.Column{"encounter_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"primary", D.Boolean{}, False{}}]},
    D.SchemaTable{"encounters", "id", [D.Column{"appointment_id", D.TextValue{}, False{}}, D.Column{"closed_at", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"reason", D.TextValue{}, False{}}]},
    D.SchemaTable{"invoices", "id", [D.Column{"amount_cents", D.Integer{}, False{}}, D.Column{"due_date", D.TextValue{}, False{}}, D.Column{"encounter_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"status", D.TextValue{}, False{}}]},
    D.SchemaTable{"patients", "id", [D.Column{"birth_date", D.TextValue{}, False{}}, D.Column{"email", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]},
    D.SchemaTable{"prescriptions", "id", [D.Column{"duration_days", D.Integer{}, False{}}, D.Column{"encounter_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"instructions", D.TextValue{}, False{}}, D.Column{"medication", D.TextValue{}, False{}}]},
    D.SchemaTable{"rooms", "id", [D.Column{"active", D.Boolean{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"location", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]},
    D.SchemaTable{"specialties", "id", [D.Column{"department", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]}]}
def limits() -> S.Limits:
  S.Limits{262144n, 8388608n, 262144n}
def config() -> S.Configuration:
  L.configuration(schema(), limits(), E.identity())
