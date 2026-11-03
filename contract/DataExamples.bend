# Closed examples of data-semantics edge cases.
import Base
import ./Data.bend as D

def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"cars", "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"model", D.TextValue{}, True{}}]}]}

def initial() -> D.State:
  D.State{[D.Table{"cars", [D.Row{"c1", [D.Field{"id", D.VText{"c1"}}, D.Field{"model", D.VAbsent{}}]}]}], Nil{}}

law state_well_formed:
  {D.structure(schema(), initial()) == True{} : Bool}

def state_well_formed():
  {==}

law row_absent_distinct:
  {D.operate(schema(), initial(), D.ReadCell{D.Application{"cars"}, "c2", "model"}) == D.Observed{D.RowAbsent{}} : D.ResultOp}

def row_absent_distinct():
  {==}

law column_absent_distinct:
  {D.operate(schema(), initial(), D.ReadCell{D.Application{"cars"}, "c1", "model"}) == D.Observed{D.Cell{D.VAbsent{}}} : D.ResultOp}

def column_absent_distinct():
  {==}

law write_in_row_absent_negative_informs:
  {D.operate(schema(), initial(), D.DefineColumn{D.Application{"cars"}, "c2", "model", D.VText{"X"}}) == D.Changed{initial()} : D.ResultOp}

def write_in_row_absent_negative_informs():
  {==}

law key_divergent_and_error_same_without_row:
  {D.operate(schema(), initial(), D.DefineColumn{D.Application{"cars"}, "c2", "id", D.VText{"other"}}) == D.FailureData{} : D.ResultOp}

def key_divergent_and_error_same_without_row():
  {==}

law table_nonexistent_and_error:
  {D.operate(schema(), initial(), D.RemoveRow{D.Application{"other"}, "c1"}) == D.FailureData{} : D.ResultOp}

def table_nonexistent_and_error():
  {==}

# U+D800 is a surrogate, therefore not a valid Unicode scalar.
law key_unicode_invalid_and_error:
  {D.operate(schema(), initial(), D.ViewExistence{D.Application{"cars"}, SCon{Chr{55296}, SNil{}}}) == D.FailureData{} : D.ResultOp}

def key_unicode_invalid_and_error():
  {==}
