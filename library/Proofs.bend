# Event retention is independent of an administrator's chosen laws.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Logic.bend as L
import ../src/Termination.bend as T

law append_extends:
  for xs: List<&2, S.OperationEvent>
  for -ev: S.OperationEvent
  L.Prefix(S.OperationEvent, xs, S.append(xs, ev))
def append_extends(xs, ev):
  match xs:
    case Nil{}: Unit{}
    case Con{h, rest}: L.Both{{==}, append_extends(rest, ev)}

# The premise identifies the result of the real operation, not authorization.
law read_continuation:
  for +n: Nat
  for +e: D.Schema
  for +s: D.State
  for +op: D.Operation
  for +obs: D.Observation
  for -k: S.Return -> S.Action
  for +ts: List<&2, S.OperationEvent>
  for result: {D.operate(e, s, op) == D.Observed{obs} : D.ResultOp}
  {S.resume_execution_trace(n, S.step(S.Access{op, k}, e, s), e, ts) ==
    T.observe(n, k(S.Datum{obs}), e, s, S.append(ts, S.OperationEvent{op, S.Reading{obs}})) : S.Trace}
def read_continuation(n, e, s, op, obs, k, ts, result):
  %Equal.sym(D.ResultOp, D.operate(e, s, op), D.Observed{obs}, result) : {S.resume_execution_trace(n, S.apply(_, s, op, k), e, ts) ==
    T.observe(n, k(S.Datum{obs}), e, s, S.append(ts, S.OperationEvent{op, S.Reading{obs}})) : S.Trace}
  T.continuation(n, s, k(S.Datum{obs}), S.OperationEvent{op, S.Reading{obs}}, e, ts)

# A later refusal retains the actual read event, for any prior history.
law read_then_refuse:
  for +e: D.Schema
  for +s: D.State
  for +op: D.Operation
  for +obs: D.Observation
  for -v: D.Value
  for +ts: List<&2, S.OperationEvent>
  for result: {D.operate(e, s, op) == D.Observed{obs} : D.ResultOp}
  {S.resume_execution_trace(1n, S.step(S.Access{op, r => S.Refuse{v}}, e, s), e, ts) ==
    S.Final{s, S.append(ts, S.OperationEvent{op, S.Reading{obs}}), S.Response{S.Refusal{}, v}} : S.Trace}
def read_then_refuse(e, s, op, obs, v, ts, result):
  read_continuation(1n, e, s, op, obs, r => S.Refuse{v}, ts, result)

# A pure filtering decision is just a continuation: it cannot undo the read.
law read_then_filter:
  for +e: D.Schema
  for +s: D.State
  for +op: D.Operation
  for +obs: D.Observation
  for -output: D.Observation -> D.Value
  for +ts: List<&2, S.OperationEvent>
  for result: {D.operate(e, s, op) == D.Observed{obs} : D.ResultOp}
  {S.resume_execution_trace(1n, S.step(S.Access{op, r => S.Finish{output(obs)}}, e, s), e, ts) ==
    S.Final{s, S.append(ts, S.OperationEvent{op, S.Reading{obs}}), S.Response{S.Success{}, output(obs)}} : S.Trace}
def read_then_filter(e, s, op, obs, output, ts, result):
  read_continuation(1n, e, s, op, obs, r => S.Finish{output(obs)}, ts, result)
