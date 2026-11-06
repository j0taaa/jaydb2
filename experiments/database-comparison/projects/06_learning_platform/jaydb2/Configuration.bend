import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Environment.bend as E
def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"assignments", "id", [D.Column{"due_on", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"lesson_id", D.TextValue{}, False{}}, D.Column{"max_score", D.Integer{}, False{}}, D.Column{"title", D.TextValue{}, False{}}]},
    D.SchemaTable{"cohorts", "id", [D.Column{"capacity", D.Integer{}, False{}}, D.Column{"course_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"starts_on", D.TextValue{}, False{}}]},
    D.SchemaTable{"courses", "id", [D.Column{"currency", D.TextValue{}, False{}}, D.Column{"fee_cents", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"instructor_id", D.TextValue{}, False{}}, D.Column{"title", D.TextValue{}, False{}}]},
    D.SchemaTable{"enrollments", "id", [D.Column{"cohort_id", D.TextValue{}, False{}}, D.Column{"enrolled_on", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"learner_id", D.TextValue{}, False{}}, D.Column{"status", D.TextValue{}, False{}}]},
    D.SchemaTable{"grades", "id", [D.Column{"feedback", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"reviewer_id", D.TextValue{}, False{}}, D.Column{"score", D.Integer{}, False{}}, D.Column{"submission_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"instructors", "id", [D.Column{"expertise", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"organization_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"learners", "id", [D.Column{"email", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}, D.Column{"organization_id", D.TextValue{}, False{}}]},
    D.SchemaTable{"lessons", "id", [D.Column{"duration_minutes", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"module_id", D.TextValue{}, False{}}, D.Column{"title", D.TextValue{}, False{}}]},
    D.SchemaTable{"modules", "id", [D.Column{"course_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"position", D.Integer{}, False{}}, D.Column{"title", D.TextValue{}, False{}}]},
    D.SchemaTable{"organizations", "id", [D.Column{"country_code", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"name", D.TextValue{}, False{}}]},
    D.SchemaTable{"payments", "id", [D.Column{"amount_cents", D.Integer{}, False{}}, D.Column{"currency", D.TextValue{}, False{}}, D.Column{"enrollment_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"status", D.TextValue{}, False{}}]},
    D.SchemaTable{"submissions", "id", [D.Column{"artifact_name", D.TextValue{}, False{}}, D.Column{"assignment_id", D.TextValue{}, False{}}, D.Column{"enrollment_id", D.TextValue{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"submitted_at", D.TextValue{}, False{}}]}]}
def limits() -> S.Limits:
  S.Limits{262144n, 8388608n, 262144n}
def config() -> S.Configuration:
  L.configuration(schema(), limits(), E.identity())
