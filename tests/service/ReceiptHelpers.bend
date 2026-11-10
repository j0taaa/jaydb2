# Functional boundaries for the reusable helper on actual Data.operate semantics.
import Base
import ../../contract/Data.bend as D
import ../../contract/Semantics.bend as S
import ../../contract/Requirements.bend as R
import ../../library/Receipts.bend as H

def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"alice", "id", [D.Column{"id", D.TextValue{}, False{}},
    D.Column{"input", D.TextValue{}, False{}}, D.Column{"operation", D.TextValue{}, False{}},
    D.Column{"result", D.TextValue{}, False{}}]}]}

def fields(key: String, input: String, operation: String, result: String) -> List<&2, D.Field>:
  [D.Field{"id", D.VText{key}}, D.Field{"input", D.VText{input}},
    D.Field{"operation", D.VText{operation}}, D.Field{"result", D.VText{result}}]

def state() -> D.State:
  D.State{[D.Table{"alice", [D.Row{"r", fields("r", "0:tea", "issue/v1", "v:r") }]}], Nil{}}

def result(r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{D.VText{v}}}: S.Finish{D.VText{v}}
    case _: S.Refuse{D.VAbsent{}}

def program(operation: String, input: String) -> S.Program:
  S.Program{ctx => args => H.bound("alice", "r", operation, input, S.Refuse{D.VText{"miss"}}, result)}

def response(p: S.Trace) -> S.Response:
  match p:
    case S.Prefix{w, ts}: S.response_error(S.Failure{})
    case S.Final{w, ts, r}: r

law exact_hit:
  {response(S.execute(4n, program("issue/v1", "0:tea"), schema(), state(), D.Context{"alice", "user"}, D.VAbsent{})) ==
    S.Response{S.Success{}, D.VText{"v:r"}} : S.Response}
def exact_hit(): {==}

law version_conflict:
  {response(S.execute(4n, program("issue/v2", "0:tea"), schema(), state(), D.Context{"alice", "user"}, D.VAbsent{})) ==
    S.Response{S.Refusal{}, D.VText{"request conflict"}} : S.Response}
def version_conflict(): {==}

law exact_input_conflict:
  {S.execute(4n, program("issue/v1", "0:tea "), schema(), state(), D.Context{"alice", "user"}, D.VAbsent{}) ==
    S.Final{state(), [S.OperationEvent{D.ReadCell{D.Application{"alice"}, "r", "input"}, S.Reading{D.Cell{D.VText{"0:tea"}}}}],
      S.Response{S.Refusal{}, D.VText{"request conflict"}}} : S.Trace}
def exact_input_conflict(): {==}

law hit_does_not_change_state:
  {S.state_execution_trace(S.execute(4n, program("issue/v1", "0:tea"), schema(), state(), D.Context{"alice", "user"}, D.VAbsent{})) == state() : D.State}
def hit_does_not_change_state(): {==}

# The first business write succeeds; the malformed second receipt write fails.
def failed_program() -> S.Program:
  S.Program{ctx => args => H.put("alice", "v", fields("v", "x", "issue/v1", "v"),
    H.put("alice", "broken", Nil{}, S.Finish{D.VText{"v"}}))}

def failed_trace() -> S.Trace:
  S.execute(3n, failed_program(), schema(), state(), D.Context{"alice", "user"}, D.VAbsent{})

law second_write_data_error:
  {response(failed_trace()) == S.response_error(S.DataError{}) : S.Response}
def second_write_data_error(): {==}

law data_error_rolls_back_business_and_receipt:
  {S.publish(response(failed_trace()), state(), S.state_execution_trace(failed_trace())) == state() : D.State}
def data_error_rolls_back_business_and_receipt(): {==}

# All three original technical ceilings remain authoritative.
def final_state_limit() -> S.Response:
  R.finalize(S.Response{S.Success{}, D.VText{"v:r"}},
    S.Configuration{schema(), S.NoneLaw{}, S.Limits{32768n, 1n, 32768n}, "test"}, state())

law state_limit_rolls_back:
  {S.publish(final_state_limit(), state(), D.State{Nil{}, Nil{}}) == state() : D.State}
def state_limit_rolls_back(): {==}

law response_limit_rolls_back:
  {S.publish(R.finalize(S.Response{S.Success{}, D.VText{"v:r"}},
    S.Configuration{schema(), S.NoneLaw{}, S.Limits{32768n, 65536n, 1n}, "test"}, state()),
    state(), D.State{Nil{}, Nil{}}) == state() : D.State}
def response_limit_rolls_back(): {==}
