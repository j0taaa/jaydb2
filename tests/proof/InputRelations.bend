# Universal reapplications of exact input decoding and envelope rejection.
import Base
import ../../contract/Bytes.bend as B
import ../../contract/Data.bend as D
import ../../contract/Protocol.bend as P
import ../../contract/Semantics.bend as S
import ../../src/Input.bend as E
import ../../src/State.bend as State
import ../../src/Request.bend as Q
import ../../src/Codec.bend as C
import ../../proof/InputRelations.bend as G

law reapply_decode_reconstructs_stages_real:
  for +bs: List<&2, U32>
  for +e: D.Schema
  for +l: S.Limits
  G.ReadyRelated(E.decode(bs, e, l), bs, e, l)
def reapply_decode_reconstructs_stages_real(bs, e, l):
  G.decode_reconstructs_stages_real(bs, e, l)

law reapply_ready_reconstructs_blocks_ceilings_state_and_request:
  for +bs: List<&2, U32>
  for +e: D.Schema
  for +l: S.Limits
  for -s: D.State
  for -r: P.Request
  for ready: {E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication}
  G.InversionReady(bs, e, l, s, r)
def reapply_ready_reconstructs_blocks_ceilings_state_and_request(bs, e, l, s, r, ready):
  G.ready_reconstructs_blocks_ceilings_state_and_request(bs, e, l, s, r, ready)

law reapply_codec_accepted_combined_envelope_invalid_excludes_request_canonical:
  for +br: List<&2, U32>
  for +body: B.Number64
  for +tr: B.Number64
  for +v: D.Value
  for +measured: {B.nat64(B.length(br)) == Some{body} : Maybe<&2, B.Number64>}
  for +fits: {C.less_equal64(body, tr) == True{} : Bool}
  for +accepted: {C.decode(br, tr) == C.Decoded{v} : C.Outcome}
  for +refused: {Q.extract(v) == None{} : Maybe<&2, P.Request>}
  G.WithoutRequestEncoded(br)
def reapply_codec_accepted_combined_envelope_invalid_excludes_request_canonical(br, body, tr, v, measured, fits, accepted, refused):
  G.codec_accepted_combined_envelope_invalid_excludes_request_canonical(br, body, tr, v, measured, fits, accepted, refused)
