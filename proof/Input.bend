# General composition of ACTUAL adapters. Hypotheses are encodings,
# actual measures/limits and structure required by the state decoder.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/RequestFacts.bend as I
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ../src/Input.bend as E
import ../src/State.bend as State
import ../src/Request.bend as Q
import ../src/Transport.bend as T
import ./Representation.bend as V
import ./Transport.bend as Transport
import ./CodecComplete.bend as Complete
import ./CodecLaw2.bend as Codec
import ./CodecOctets.bend as Octets
import ./Foundations.bend as F
import ./Authentication.bend as A
import ./InputMeasure.bend as Measure

# Composition lemma: none of the hypotheses is already the Input conclusion.
law stages_real_produce_ready_exact:
  for +bs: List<&2, U32>
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +e: D.Schema
  for +l: S.Limits
  for +te: B.Number64
  for +tr: B.Number64
  for +ve: D.Value
  for +vr: D.Value
  for +s: D.State
  for +r: P.Request
  for separate: {T.separate(bs) == Some{T.Parts{be, br}} : Maybe<&2, T.Parts>}
  for ceiling_and: {B.nat64(R.limit_state(l)) == Some{te} : Maybe<&2, B.Number64>}
  for ceiling_r: {B.nat64(R.limit_message(l)) == Some{tr} : Maybe<&2, B.Number64>}
  for state_bytes: {C.decode(be, te) == C.Decoded{ve} : C.Outcome}
  for state_value: {State.decode(ve, e) == Some{s} : Maybe<&2, D.State>}
  for +message_bytes: {C.decode(br, tr) == C.Decoded{vr} : C.Outcome}
  for envelope: {Q.extract(vr) == Some{r} : Maybe<&2, P.Request>}
  {E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication}
def stages_real_produce_ready_exact(bs, be, br, e, l, te, tr, ve, vr, s, r,
  separate, ceiling_and, ceiling_r, state_bytes, state_value, message_bytes, envelope):
  %Equal.sym(Maybe<&2, T.Parts>, T.separate(bs), Some{T.Parts{be, br}}, separate) :
    {E.parts(_, e, l) == E.InputReady{s, r} : E.PreAuthentication}
  %Equal.sym(Maybe<&2, B.Number64>, B.nat64(R.limit_state(l)), Some{te}, ceiling_and) :
    {E.read_state(_, e, be, br, B.nat64(R.limit_message(l))) == E.InputReady{s, r} : E.PreAuthentication}
  %Equal.sym(C.Outcome, C.decode(be, te), C.Decoded{ve}, state_bytes) :
    {E.state_decoded(_, e, br, B.nat64(R.limit_message(l))) == E.InputReady{s, r} : E.PreAuthentication}
  %Equal.sym(Maybe<&2, D.State>, State.decode(ve, e), Some{s}, state_value) :
    {E.state_read(_, br, B.nat64(R.limit_message(l))) == E.InputReady{s, r} : E.PreAuthentication}
  %Equal.sym(Maybe<&2, B.Number64>, B.nat64(R.limit_message(l)), Some{tr}, ceiling_r) :
    {E.read_message(_, br, s) == E.InputReady{s, r} : E.PreAuthentication}
  %Equal.sym(E.PreAuthentication, E.read_message(Some{tr}, br, s), E.message(C.decode(br, tr), s),
    Measure.decoding_accepts_preserves_message(br, tr, s, vr, message_bytes)) :
    {_ == E.InputReady{s, r} : E.PreAuthentication}
  %Equal.sym(C.Outcome, C.decode(br, tr), C.Decoded{vr}, message_bytes) :
    {E.message(_, s) == E.InputReady{s, r} : E.PreAuthentication}
  %Equal.sym(Maybe<&2, P.Request>, Q.extract(vr), Some{r}, envelope) :
    {E.envelope(_, s) == E.InputReady{s, r} : E.PreAuthentication}
  {==}

# No premise assumes success of Codec, Input, authentication or Contract.
# Envelope and byte validity are DERIVED from original encoding.
law bytes_canonical_assembled_produce_ready_exact:
  for +e: D.Schema
  for +s: D.State
  for +r: P.Request
  for +l: S.Limits
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +bs: List<&2, U32>
  for +ce: B.Number64
  for +cr: B.Number64
  for +te: B.Number64
  for +tr: B.Number64
  for cod_and: P.Encoding(D.state_value(s), be)
  for cod_r: P.Encoding(P.request_value(r), br)
  for assembly: {T.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for measure_and: {B.nat64(B.length(be)) == Some{ce} : Maybe<&2, B.Number64>}
  for measure_r: {B.nat64(B.length(br)) == Some{cr} : Maybe<&2, B.Number64>}
  for ceiling_and: {B.nat64(R.limit_state(l)) == Some{te} : Maybe<&2, B.Number64>}
  for ceiling_r: {B.nat64(R.limit_message(l)) == Some{tr} : Maybe<&2, B.Number64>}
  for fits_and: {C.less_equal64(ce, te) == True{} : Bool}
  for fits_r: {C.less_equal64(cr, tr) == True{} : Bool}
  for structure: {D.structure(e, s) == True{} : Bool}
  {E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication}
def bytes_canonical_assembled_produce_ready_exact(e, s, r, l, be, br, bs, ce, cr, te, tr,
  cod_and, cod_r, assembly, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure):
  +canon_and = {cod_and : {P.encode(D.state_value(s)) == Some{be} : Maybe<&2, List<&2, U32>>}}
  +dec_r = Complete.all_encoding_canonical_representable_and_decoded(
    P.request_value(r), br, cr, tr, cod_r, measure_r, fits_r)
  F.combined_pair({E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication},
    P.Encoding(P.request_value(r), br), {D.value_valid(P.request_value(r)) == True{} : Bool},
    Codec.acceptance_reconstitutes_encoding_original_and_validity(br, tr, P.request_value(r), dec_r),
    canonical => is_valid => stages_real_produce_ready_exact(bs, be, br, e, l, te, tr,
      D.state_value(s), P.request_value(r), s, r,
      Transport.separate_inverts_all_assembly_is_valid(be, br, bs, assembly,
        Octets.any_encoding_only_emits_octets(D.state_value(s), be, canon_and),
        Octets.any_encoding_only_emits_octets(P.request_value(r), br, canonical)),
      ceiling_and, ceiling_r,
      Complete.all_encoding_canonical_representable_and_decoded(D.state_value(s), be, ce, te, canon_and, measure_and, fits_and),
      V.transport_private_preserves_state(e, s, structure), dec_r,
      V.request_is_valid_preserves_all_os_fields(r, is_valid)))

# The state measure alone suffices for assembly to exist; there is no new
# quota on the private sum header + state + request.
def AssemblyExists(-be: List<&2, U32>, -br: List<&2, U32>) -> Type:
  &bs: List<&2, U32> -> {T.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}

law measure_of_state_guarantees_assembly:
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for ce: B.Number64
  for measure: {B.nat64(B.length(be)) == Some{ce} : Maybe<&2, B.Number64>}
  AssemblyExists(be, br)
def measure_of_state_guarantees_assembly(be, br, ce, measure):
  match ce:
    case B.Number64{high, low}:
      (B.concatenate(B.be64(high, low), B.concatenate(be, br)),
      (%Equal.sym(Maybe<&2, B.Number64>, B.nat64(B.length(be)), Some{B.Number64{high, low}}, measure) :
        {T.join_combined_header(B.number64_bytes(_), be, br) ==
          Some{B.concatenate(B.be64(high, low), B.concatenate(be, br))} : Maybe<&2, List<&2, U32>>}
      {==}))

# Exact equality for EVERY state/request, including working states
# with temporary credentials. Requires no structure/publishability here.
law authenticate_preserves_exactly_state_request_and_context:
  for +s: D.State
  for r: P.Request
  {E.authenticate(Some{r}, s) == E.identity(D.authenticate(s, I.credential(r)), s, r) : E.Analysis}
def authenticate_preserves_exactly_state_request_and_context(s, r):
  match r:
    case P.Request{cred, cod, args, pi}:
      {==}

law analyze_ready_and_authentication_stable_exact:
  for +bs: List<&2, U32>
  for +e: D.Schema
  for +l: S.Limits
  for +s: D.State
  for +r: P.Request
  for ready: {E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication}
  {E.analyze(bs, e, l) == E.identity(D.authenticate(s, I.credential(r)), s, r) : E.Analysis}
def analyze_ready_and_authentication_stable_exact(bs, e, l, s, r, ready):
  %Equal.sym(E.PreAuthentication, E.decode(bs, e, l), E.InputReady{s, r}, ready) :
    {E.authenticate_pre(_) == E.identity(D.authenticate(s, I.credential(r)), s, r) : E.Analysis}
  authenticate_preserves_exactly_state_request_and_context(s, r)

law analyze_accepts_exactly_context_authenticated:
  for +bs: List<&2, U32>
  for +e: D.Schema
  for +l: S.Limits
  for +s: D.State
  for +r: P.Request
  for +ctx: D.Context
  for ready: {E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication}
  for aut: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}
  {E.analyze(bs, e, l) == E.Received{s, r, ctx} : E.Analysis}
def analyze_accepts_exactly_context_authenticated(bs, e, l, s, r, ctx, ready, aut):
  Equal.trans(E.Analysis, E.analyze(bs, e, l), E.identity(D.authenticate(s, I.credential(r)), s, r),
    E.Received{s, r, ctx}, analyze_ready_and_authentication_stable_exact(bs, e, l, s, r, ready),
    Equal.cong(Maybe<&2, D.Context>, E.Analysis, q => E.identity(q, s, r),
      D.authenticate(s, I.credential(r)), Some{ctx}, aut))

law analyze_refusal_exactly_authentication_absent:
  for +bs: List<&2, U32>
  for +e: D.Schema
  for +l: S.Limits
  for +s: D.State
  for +r: P.Request
  for ready: {E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication}
  for aut: {D.authenticate(s, I.credential(r)) == None{} : Maybe<&2, D.Context>}
  {E.analyze(bs, e, l) == E.Rejected{S.Authentication{}} : E.Analysis}
def analyze_refusal_exactly_authentication_absent(bs, e, l, s, r, ready, aut):
  Equal.trans(E.Analysis, E.analyze(bs, e, l), E.identity(D.authenticate(s, I.credential(r)), s, r),
    E.Rejected{S.Authentication{}}, analyze_ready_and_authentication_stable_exact(bs, e, l, s, r, ready),
    Equal.cong(Maybe<&2, D.Context>, E.Analysis, q => E.identity(q, s, r),
      D.authenticate(s, I.credential(r)), None{}, aut))

law analyze_ready_publishable_refusal_credential_empty:
  for +bs: List<&2, U32>
  for +e: D.Schema
  for +l: S.Limits
  for +s: D.State
  for +r: P.Request
  for ready: {E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication}
  for structure: {D.structure(e, s) == True{} : Bool}
  for empty: {I.credential(r) == "" : String}
  {E.analyze(bs, e, l) == E.Rejected{S.Authentication{}} : E.Analysis}
def analyze_ready_publishable_refusal_credential_empty(bs, e, l, s, r, ready, structure, empty):
  analyze_refusal_exactly_authentication_absent(bs, e, l, s, r, ready,
    (%Equal.sym(String, I.credential(r), "", empty) :
      {D.authenticate(s, _) == None{} : Maybe<&2, D.Context>}
      A.state_publishable_negative_authenticates_empty(e, s, structure)))

# Complete composition without receiving InputReady or analyze as a hypothesis.
law bytes_canonical_assembled_are_analyzed_combined_identity_exact:
  for +e: D.Schema
  for +s: D.State
  for +r: P.Request
  for +l: S.Limits
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +bs: List<&2, U32>
  for +ce: B.Number64
  for +cr: B.Number64
  for +te: B.Number64
  for +tr: B.Number64
  for cod_and: P.Encoding(D.state_value(s), be)
  for cod_r: P.Encoding(P.request_value(r), br)
  for assembly: {T.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for measure_and: {B.nat64(B.length(be)) == Some{ce} : Maybe<&2, B.Number64>}
  for measure_r: {B.nat64(B.length(br)) == Some{cr} : Maybe<&2, B.Number64>}
  for ceiling_and: {B.nat64(R.limit_state(l)) == Some{te} : Maybe<&2, B.Number64>}
  for ceiling_r: {B.nat64(R.limit_message(l)) == Some{tr} : Maybe<&2, B.Number64>}
  for fits_and: {C.less_equal64(ce, te) == True{} : Bool}
  for fits_r: {C.less_equal64(cr, tr) == True{} : Bool}
  for structure: {D.structure(e, s) == True{} : Bool}
  L.E<{E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication},
    {E.analyze(bs, e, l) == E.identity(D.authenticate(s, I.credential(r)), s, r) : E.Analysis}>
def bytes_canonical_assembled_are_analyzed_combined_identity_exact(e, s, r, l, be, br, bs, ce, cr, te, tr,
  cod_and, cod_r, assembly, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure):
  +ready = bytes_canonical_assembled_produce_ready_exact(e, s, r, l, be, br, bs, ce, cr, te, tr,
    cod_and, cod_r, assembly, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure)
  L.Both{ready, analyze_ready_and_authentication_stable_exact(bs, e, l, s, r, ready)}

# Assembly need not be assumed: the actual measure itself supplies
# a concrete packet witness with exact InputReady and analyze.
def PacketReady(-e: D.Schema, -s: D.State, -r: P.Request,
  -l: S.Limits, -be: List<&2, U32>, -br: List<&2, U32>) -> Type:
  &bs: List<&2, U32> -> L.E<{T.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
    L.E<{E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication},
      {E.analyze(bs, e, l) == E.identity(D.authenticate(s, I.credential(r)), s, r) : E.Analysis}>>


def construct_packet_ready(+e: D.Schema, +s: D.State, +r: P.Request,
  +l: S.Limits, +be: List<&2, U32>, +br: List<&2, U32>,
  +ce: B.Number64, +cr: B.Number64, +te: B.Number64, +tr: B.Number64,
  cod_and: P.Encoding(D.state_value(s), be), cod_r: P.Encoding(P.request_value(r), br),
  measure_and: {B.nat64(B.length(be)) == Some{ce} : Maybe<&2, B.Number64>},
  measure_r: {B.nat64(B.length(br)) == Some{cr} : Maybe<&2, B.Number64>},
  ceiling_and: {B.nat64(R.limit_state(l)) == Some{te} : Maybe<&2, B.Number64>},
  ceiling_r: {B.nat64(R.limit_message(l)) == Some{tr} : Maybe<&2, B.Number64>},
  fits_and: {C.less_equal64(ce, te) == True{} : Bool},
  fits_r: {C.less_equal64(cr, tr) == True{} : Bool},
  structure: {D.structure(e, s) == True{} : Bool},
  assembled: AssemblyExists(be, br)) -> PacketReady(e, s, r, l, be, br):
  match assembled:
    case (+bs, assembly_result):
      +assembly = {assembly_result : {T.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}}
      (bs, L.Both{assembly,
        bytes_canonical_assembled_are_analyzed_combined_identity_exact(e, s, r, l, be, br, bs, ce, cr, te, tr,
          cod_and, cod_r, assembly, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure)})

law all_input_canonical_admissible_has_packet_ready_and_analysis_exact:
  for +e: D.Schema
  for +s: D.State
  for +r: P.Request
  for +l: S.Limits
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +ce: B.Number64
  for +cr: B.Number64
  for +te: B.Number64
  for +tr: B.Number64
  for cod_and: P.Encoding(D.state_value(s), be)
  for cod_r: P.Encoding(P.request_value(r), br)
  for +measure_and: {B.nat64(B.length(be)) == Some{ce} : Maybe<&2, B.Number64>}
  for measure_r: {B.nat64(B.length(br)) == Some{cr} : Maybe<&2, B.Number64>}
  for ceiling_and: {B.nat64(R.limit_state(l)) == Some{te} : Maybe<&2, B.Number64>}
  for ceiling_r: {B.nat64(R.limit_message(l)) == Some{tr} : Maybe<&2, B.Number64>}
  for fits_and: {C.less_equal64(ce, te) == True{} : Bool}
  for fits_r: {C.less_equal64(cr, tr) == True{} : Bool}
  for structure: {D.structure(e, s) == True{} : Bool}
  PacketReady(e, s, r, l, be, br)
def all_input_canonical_admissible_has_packet_ready_and_analysis_exact(e, s, r, l, be, br, ce, cr, te, tr,
  cod_and, cod_r, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure):
  construct_packet_ready(e, s, r, l, be, br, ce, cr, te, tr,
    cod_and, cod_r, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure,
    measure_of_state_guarantees_assembly(be, br, ce, measure_and))
