# Deliberately false semantic claim; this must reject at the proof body.
import Base
import ../../../library/QuerySelectionModel.bend as Meaning
import ../../../library/QueryReadPlanProperties.bend as Props
import ../../../library/QueryReadPlan.bend as Plan
import ../../../library/ReadProgramProofs.bend as Total
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/ReadProgram.bend as P
import ../../../src/Termination.bend as T

def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"t","id",[D.Column{"a",D.TextValue{},True{}}]}]}

def state(value: D.Value) -> D.State:
  D.State{[D.Table{"t",[D.Row{"k",[D.Field{"a",value}]}]}],Nil{}}

law false_reject_source_plan_ignores_failure:
  {Plan.plan(schema(),state(D.VAbsent{}),D.Application{"t"},"k",["z"]) == Plan.ReadsReady{Meaning.Clear{},D.VRecordEmpty{},Nil{}} : Plan.Plan}
def false_reject_source_plan_ignores_failure(): {==}
