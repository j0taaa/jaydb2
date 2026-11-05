# Test-only oracle over recovered private bytes. Uses the SAME Core.advance
# interpreter and Voucher.program as the real worker, retaining actual events.
import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Protocol.bend as P
import ./Input.bend as Input
import ./Core.bend as Core
import ./Configuration.bend as C
import ./Voucher.bend as Voucher
import ./Native.bend as Native

def writes(+key:String,events:List<&2,S.OperationEvent>) -> U32:
  match events:
    case Nil{}: 0
    case Con{S.OperationEvent{D.DefineRow{D.Application{"alice"},k,fields},S.Write{}},rest}:
      U32.add(Bool.pick(U32,String.eq(key,k),1,0),writes(key,rest))
    case Con{other,rest}: writes(key,rest)

def summarize(trace:S.Trace) -> D.Value:
  match trace:
    case S.Final{state,+events,response}:
      D.VRecord{"business_writes",D.VInt{0,writes("v:lost",events)},
        D.VRecord{"receipt_writes",D.VInt{0,writes("r:lost",events)},
          D.VRecord{"response",S.response_value(response),D.VRecordEmpty{}}}}
    case S.Prefix{state,events}: D.VText{"unfinished trace"}

def analyze(input:Input.Analysis) -> D.Value:
  match input:
    case Input.Received{state,P.Request{credential,code,args,proof},ctx}:
      summarize(Core.traverse(16n,Core.start(Voucher.program(),ctx,args,state),C.schema()))
    case _: D.VText{"invalid test input"}

def output(bytes:Maybe<&2,List<&2,U32>>) -> List<&2,U32>:
  match bytes:
    case Some{xs}: xs
    case None{}: []

def main() -> IO(Unit):
  do IO<Unit>:
    bytes:List<&2,U32> <- Native.read()
    Native.write(output(P.encode(analyze(Input.analyze(bytes,C.schema(),C.limits())))))
