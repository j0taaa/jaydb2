import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Environment.bend as E
def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"accounts", "id", [D.Column{"active", D.Boolean{}, False{}}, D.Column{"currency", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"kind", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"opening_balance_cents", D.Integer{}, False{}}]},
    D.SchemaTable{"categories", "id", [D.Column{"essential", D.Boolean{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"monthly_budget_cents", D.Integer{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]},
    D.SchemaTable{"transactions", "id", [D.Column{"account_id", D.TextValue{}, False{}}, D.Column{"amount_cents", D.Integer{}, False{}}, D.Column{"category_id", D.TextValue{}, False{}}, D.Column{"description", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"posted_on", D.TextValue{}, False{}}]}]}
def limits() -> S.Limits:
  S.Limits{262144n, 8388608n, 262144n}
def config() -> S.Configuration:
  L.configuration(schema(), limits(), E.identity())
