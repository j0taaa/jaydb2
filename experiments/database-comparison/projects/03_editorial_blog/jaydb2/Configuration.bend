import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Environment.bend as E
def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"authors", "id", [D.Column{"active", D.Boolean{}, False{}}, D.Column{"email", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"role", D.TextValue{}, False{}}]},
    D.SchemaTable{"comments", "id", [D.Column{"approved", D.Boolean{}, False{}}, D.Column{"body", D.TextValue{}, False{}}, D.Column{"created_on", D.TextValue{}, False{}}, D.Column{"display_name", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"post_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"posts", "id", [D.Column{"author_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"published_on", D.TextValue{}, False{}}, D.Column{"reading_minutes", D.Integer{}, False{}}, D.Column{"section_id", D.TextValue{}, False{}}, D.Column{"title", D.TextValue{}, False{}}]},
    D.SchemaTable{"revisions", "id", [D.Column{"editor_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"post_id", D.TextValue{}, False{}}, D.Column{"revised_on", D.TextValue{}, False{}}, D.Column{"revision_number", D.Integer{}, False{}}, D.Column{"summary", D.TextValue{}, False{}}]},
    D.SchemaTable{"sections", "id", [D.Column{"display_order", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"slug", D.TextValue{}, False{}}]}]}
def limits() -> S.Limits:
  S.Limits{262144n, 8388608n, 262144n}
def config() -> S.Configuration:
  L.configuration(schema(), limits(), E.identity())
