# Deterministic logical decode AFTER bounded physical reception and selection.
# The private-state transport roundtrip and real read chunks are separate IO
# refinements; current is the semantic snapshot passed to actual read_message.
import Base
import ../../../../contract/Bytes.bend as B
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/PreparedProtocol.bend as W
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Requirements.bend as R
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../../src/Input.bend as Input
import ../../../PrimitivesService.bend as Micro
import ../../../ProtocolService.bend as Q

type Decision is Data:
  Shutdown{}
  Reject{prepared: Bool, status: S.Status, closes: Bool}
  Parsed{wire: W.WireRequest}
  TransportStopped{}

type DecodeRun is Data:
  DecodeRun{decision: Decision, frames: List<&2, Q.Frame>}

def decision(run: DecodeRun) -> Decision:
  DecodeRun{decision, frames} = run
  decision

def frames(run: DecodeRun) -> List<&2, Q.Frame>:
  DecodeRun{decision, frames} = run
  frames

def prepared(operation: Maybe<&2, W.Operation>) -> Bool:
  match operation:
    case None{}: False{}
    case Some{operation}: True{}

def wire(operation: Maybe<&2, W.Operation>, request: P.Request) -> W.WireRequest:
  match operation:
    case None{}: W.Ordinary{request}
    case Some{operation}: W.Extension{operation, request}

def message(operation: Maybe<&2, W.Operation>, input: Input.PreAuthentication) -> Decision:
  match input:
    case Input.InputReady{state, request}: Parsed{wire(operation, request)}
    case Input.ErrorMessage{status}: Reject{prepared(operation), status, False{}}
    case Input.ErrorTransport{}: TransportStopped{}

def limited(limit: Maybe<&2, B.Number64>, current: D.State, operation: Maybe<&2, W.Operation>, +bytes: List<&2, U32>) -> DecodeRun:
  match limit:
    case None{}: DecodeRun{TransportStopped{}, Nil{}}
    case Some{+ceiling}:
      DecodeRun{message(operation, Input.read_message(Some{ceiling}, bytes, current)), Micro.expand(Micro.Decode{bytes, ceiling})}

def routed(~c: S.Configuration, current: D.State, route: W.Dispatch) -> DecodeRun:
  match route:
    case W.InvalidExtension{}: DecodeRun{Reject{True{}, S.Input{}, False{}}, Nil{}}
    case W.OrdinaryBody{bytes}: limited(B.nat64(R.limit_message(S.limits(c))), current, None{}, bytes)
    case W.ExtensionBody{operation, bytes}: limited(B.nat64(R.limit_message(S.limits(c))), current, Some{operation}, bytes)

def disposed(~c: S.Configuration, current: D.State, disposition: X.Disposition) -> DecodeRun:
  match disposition:
    case X.CloseWithoutResponse{}: DecodeRun{Shutdown{}, Nil{}}
    case X.RefuseClose{status}: DecodeRun{Reject{False{}, status, True{}}, Nil{}}
    case X.RefuseContinue{status}: DecodeRun{Reject{False{}, status, False{}}, Nil{}}
    case X.ProcessBody{bytes}: routed(c, current, W.route_dispatch(bytes))

def run(~c: S.Configuration, current: D.State, input: X.Reception) -> DecodeRun:
  disposed(c, current, X.decide_reception(c, input))

law semantic_decoding_uses_the_full_physical_body_before_stripping:
  for ~c: S.Configuration
  for -current: D.State
  for -input: X.Reception
  {run(c, current, input) == disposed(c, current, X.decide_reception(c, input)) : DecodeRun}
def semantic_decoding_uses_the_full_physical_body_before_stripping(c, current, input):
  {==}

law ordinary_canonical_decoding_never_becomes_an_extension_by_its_code_text:
  for -current: D.State
  for -request: P.Request
  {message(None{}, Input.InputReady{current, request}) == Parsed{W.Ordinary{request}} : Decision}
def ordinary_canonical_decoding_never_becomes_an_extension_by_its_code_text(current, request):
  {==}
