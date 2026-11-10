# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Action.bend as A
import ../../../library/Mutation.bend as M
import ../../../library/Value.bend as V

def collection() -> D.Collection: D.Application{"t"}

def int_done(x: V.Int64) -> S.Action: S.Finish{V.int_value(x)}

law false_reject_counter_overflow_wraps:
  {M.counter_read(collection(),"k","count",V.Int64{0,1},int_done,S.Datum{D.Cell{D.VInt{2147483647,4294967295}}}) == S.Access{D.DefineColumn{collection(),"k","count",D.VInt{2147483648,0}},r => A.written(int_done(V.Int64{2147483648,0}),r)} : S.Action}
def false_reject_counter_overflow_wraps(): {==}
