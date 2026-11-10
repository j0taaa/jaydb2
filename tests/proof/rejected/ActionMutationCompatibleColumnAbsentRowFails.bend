# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../contract/Data.bend as D

def collection() -> D.Collection: D.Application{"t"}

def rowsstate(rows: List<&2,D.Row>) -> D.State:
  D.State{[D.Table{"t",rows}],Nil{}}

def counterschema(kind: D.ColumnKind) -> D.Schema:
  D.Schema{[D.SchemaTable{"t","id",[D.Column{"count",kind,False{}},D.Column{"id",D.TextValue{},False{}}]}]}

law false_reject_compatible_column_absent_row_fails:
  {D.operate(counterschema(D.Integer{}),rowsstate(Nil{}),D.DefineColumn{collection(),"k","count",D.VInt{0,1}}) == D.FailureData{} : D.ResultOp}
def false_reject_compatible_column_absent_row_fails(): {==}
