# An actual decoder decision never combines prepared mode with closes=True.
# Physical length/encoding validity is NOT assumed for this source property.
import Base
import ../../../../../contract/Bytes.bend as Bytes
import ../../../../../contract/Data.bend as D
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Requirements.bend as R
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../../src/Input.bend as Input
import ../../../model/serial/Decode.bend as Decode
import ./RuntimeBase.bend as Runt

def Safe(decision: Decode.Decision) -> Type:
  match decision:
    case Decode.Reject{mode, status, closes}: Runt.SafeClosing(mode, closes)
    case _: Unit

def message(+operation: Maybe<&2, W.Operation>, input: Input.PreAuthentication) -> Safe(Decode.message(operation, input)):
  match input:
    case Input.InputReady{state, request}: Unit{}
    case Input.ErrorMessage{status}: Runt.false_is_safe(Decode.prepared(operation))
    case Input.ErrorTransport{}: Unit{}

def limited(limit: Maybe<&2, Bytes.Number64>, +current: D.State, +operation: Maybe<&2, W.Operation>, +bytes: List<&2, U32>) ->
  Safe(Decode.decision(Decode.limited(limit, current, operation, bytes))):
  match limit:
    case None{}: Unit{}
    case Some{ceiling}: message(operation, Input.read_message(Some{ceiling}, bytes, current))

def routed(~c: S.Configuration, +current: D.State, route: W.Dispatch) -> Safe(Decode.decision(Decode.routed(c, current, route))):
  match route:
    case W.InvalidExtension{}: {==}
    case W.OrdinaryBody{bytes}: limited(Bytes.nat64(R.limit_message(S.limits(c))), current, None{}, bytes)
    case W.ExtensionBody{operation, bytes}: limited(Bytes.nat64(R.limit_message(S.limits(c))), current, Some{operation}, bytes)

def disposed(~c: S.Configuration, +current: D.State, disposition: X.Disposition) -> Safe(Decode.decision(Decode.disposed(c, current, disposition))):
  match disposition:
    case X.CloseWithoutResponse{}: Unit{}
    case X.RefuseClose{status}: Unit{}
    case X.RefuseContinue{status}: Unit{}
    case X.ProcessBody{bytes}: routed(c, current, W.route_dispatch(bytes))

def actual(~c: S.Configuration, +current: D.State, +input: X.Reception) -> Safe(Decode.decision(Decode.run(c, current, input))):
  disposed(c, current, X.decide_reception(c, input))
