# Prepare length induction: containers preserve original segments
# and child paths, without assuming their canonicity.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecTrace.bend as R
import ./CodecArities.bend as A
import ./CodecAssembly.bend as M
import ./CodecLimitsSequences.bend as S
import ./CodecWordsBE64.bend as K
import ./CodecPrimitives.bend as U
import ./CodecAcceptanceTags.bend as T
import ./CodecAcceptanceWord.bend as W
import ./CodecAcceptanceRoot.bend as Rz
import ./CodecAcceptanceChildren.bend as H
import ./CodecAcceptanceList.bend as I
import ./CodecAcceptanceRecord.bend as G

type Branch<-bs: List<&2, U32>, -v: D.Value, -n: Nat> is Type:
  Canonical{encoding: P.Encoding(v, bs)}
  ListFrame{number: B.Number64, xs: List<&2, S.ValueSegmented>,
    bytes: {bs == M.prefix(5, number, S.bytes_values(xs)) : List<&2, U32>},
    delivery: {A.deliver_values(S.values(xs), C.open_variable(C.zero64(number), C.CountsList{}, number, C.Root{})) == C.DecodedReady{v} : C.Machine},
    children: H.ChildrenRead(xs, n),
    octets: {B.octets_all_valid(S.bytes_values(xs)) == True{} : Bool}}
  Record{number: B.Number64, xs: List<&2, S.FieldSegmented>,
    bytes: {bs == M.prefix(6, number, S.bytes_fields(xs)) : List<&2, U32>},
    delivery: {A.deliver_fields(S.fields(xs), C.open_variable(C.zero64(number), C.CountsRecord{}, number, C.Root{})) == C.DecodedReady{v} : C.Machine},
    fields: G.FieldsRead(xs, n),
    octets: {B.octets_all_valid(S.bytes_fields(xs)) == True{} : Bool}}

def expand_child(-v: D.Value, +bs: List<&2, U32>, +less: Nat, +greater: Nat,
  limit: {Nat.is_le(less, greater) == True{} : Bool},
  child: H.ChildRead<v, bs, less>) -> H.ChildRead<v, bs, greater>:
  match child:
    case H.ChildRead{body, ceiling, outside, local, bound}:
      H.ChildRead{body, ceiling, outside, local,
        S.limit_transitive(B.length(bs), less, greater, bound, limit)}

law expand_children:
  for xs: List<&2, S.ValueSegmented>
  for +less: Nat
  for +greater: Nat
  for +limit: {Nat.is_le(less, greater) == True{} : Bool}
  for children: H.ChildrenRead(xs, less)
  H.ChildrenRead(xs, greater)
def expand_children(xs, less, greater, limit, children):
  match xs:
    case Nil{}:
      Unit{}
    case Con{S.ValueSegmented{v, +bs}, +t}:
      L.Both{child, tail} = children
      L.Both{expand_child(v, bs, less, greater, limit, child),
        expand_children(t, less, greater, limit, tail)}

law expand_fields:
  for xs: List<&2, S.FieldSegmented>
  for +less: Nat
  for +greater: Nat
  for +limit: {Nat.is_le(less, greater) == True{} : Bool}
  for fields: G.FieldsRead(xs, less)
  G.FieldsRead(xs, greater)
def expand_fields(xs, less, greater, limit, fields):
  match xs:
    case Nil{}:
      Unit{}
    case Con{S.FieldSegmented{name, v, nb, +vb}, +t}:
      L.Both{valid, rest} = fields
      L.Both{canonical, read} = rest
      L.Both{child, tail} = read
      L.Both{valid, L.Both{canonical,
        L.Both{expand_child(v, vb, less, greater, limit, child),
          expand_fields(t, less, greater, limit, tail)}}}

def prepare_list_segmented(+n: Nat, +bs: List<&2, U32>, +number: B.Number64,
  +payload: List<&2, U32>, -v: D.Value,
  factoring: {Con{5, bs} == M.prefix(5, number, payload) : List<&2, U32>},
  limit: {Nat.is_le(B.length(payload), n) == True{} : Bool},
  all_valid: {B.octets_all_valid(payload) == True{} : Bool},
  segmentation: I.Segmentation<payload,
    C.open_variable(C.zero64(number), C.CountsList{}, number, C.Root{}), v, B.length(payload)>) ->
  Branch<Con{5, bs}, v, n>:
  match segmentation:
    case I.Segmentation{+xs, +bytes, delivery, children}:
      ListFrame{number, xs,
        Equal.trans(List<&2, U32>, Con{5, bs}, M.prefix(5, number, payload),
          M.prefix(5, number, S.bytes_values(xs)), factoring,
          Equal.cong(List<&2, U32>, List<&2, U32>, t => M.prefix(5, number, t),
            payload, S.bytes_values(xs), bytes)),
        delivery, expand_children(xs, B.length(payload), n, limit, children),
        (%bytes : {B.octets_all_valid(_) == True{} : Bool}
          all_valid)}

def prepare_record_segmented(+n: Nat, +bs: List<&2, U32>, +number: B.Number64,
  +payload: List<&2, U32>, -v: D.Value,
  factoring: {Con{6, bs} == M.prefix(6, number, payload) : List<&2, U32>},
  limit: {Nat.is_le(B.length(payload), n) == True{} : Bool},
  all_valid: {B.octets_all_valid(payload) == True{} : Bool},
  segmentation: G.Segmentation<payload,
    C.open_variable(C.zero64(number), C.CountsRecord{}, number, C.Root{}), v, B.length(payload)>) ->
  Branch<Con{6, bs}, v, n>:
  match segmentation:
    case G.Segmentation{+xs, +bytes, delivery, fields}:
      Record{number, xs,
        Equal.trans(List<&2, U32>, Con{6, bs}, M.prefix(6, number, payload),
          M.prefix(6, number, S.bytes_fields(xs)), factoring,
          Equal.cong(List<&2, U32>, List<&2, U32>, t => M.prefix(6, number, t),
            payload, S.bytes_fields(xs), bytes)),
        delivery, expand_fields(xs, B.length(payload), n, limit, fields),
        (%bytes : {B.octets_all_valid(_) == True{} : Bool}
          all_valid)}

def prepare_list_extracted(+n: Nat, +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  limit: {Nat.is_le(B.length(bs), n) == True{} : Bool},
  extracted: W.WordExtracted<bs, C.CountsList{}, C.Root{}, body, ceiling, v>) -> Branch<Con{5, bs}, v, n>:
  match extracted:
    case W.Extracted{a, b, c, d, e, f0, g, h, +payload, +high, +low,
      factoring, octets, rest_valid, number, be64, +factoring_be64, frame, execution, +ready}:
      +q = {B.Number64{high, low} : B.Number64}
      +cpost = K.decrease(8n, body)
      +tpost = K.decrease(8n, ceiling)
      fits = Rz.check_accepts_and_fits(
        C.check(C.sum_optional(C.minimum_field(C.CountsList{}, q), C.minimum_stack(C.Root{})), cpost, tpost),
        payload, cpost, tpost, C.CountsList{}, q, C.Root{}, v, ready)
      prepare_list_segmented(n, bs, q, payload, v,
        Equal.cong(List<&2, U32>, List<&2, U32>, t => Con{5, t}, bs,
          B.concatenate(B.be64(high, low), payload), factoring_be64),
        H.limit_suffix(B.be64(high, low), payload, n,
          H.limit_of_bytes_equal(bs, B.concatenate(B.be64(high, low), payload), n, factoring_be64, limit)),
        rest_valid,
        I.list_accepts_extracts_all_os_children(payload, cpost, tpost, q, v,
          (%fits : {R.machine(R.execute(payload,
            R.Frame{cpost, tpost, C.open_checked(_, C.CountsList{}, q, C.Root{})})) == C.DecodedReady{v} : C.Machine}
            ready)))

def prepare_record_extracted(+n: Nat, +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  limit: {Nat.is_le(B.length(bs), n) == True{} : Bool},
  extracted: W.WordExtracted<bs, C.CountsRecord{}, C.Root{}, body, ceiling, v>) -> Branch<Con{6, bs}, v, n>:
  match extracted:
    case W.Extracted{a, b, c, d, e, f0, g, h, +payload, +high, +low,
      factoring, octets, +rest_valid, number, be64, +factoring_be64, frame, execution, +ready}:
      +q = {B.Number64{high, low} : B.Number64}
      +cpost = K.decrease(8n, body)
      +tpost = K.decrease(8n, ceiling)
      fits = Rz.check_accepts_and_fits(
        C.check(C.sum_optional(C.minimum_field(C.CountsRecord{}, q), C.minimum_stack(C.Root{})), cpost, tpost),
        payload, cpost, tpost, C.CountsRecord{}, q, C.Root{}, v, ready)
      prepare_record_segmented(n, bs, q, payload, v,
        Equal.cong(List<&2, U32>, List<&2, U32>, t => Con{6, t}, bs,
          B.concatenate(B.be64(high, low), payload), factoring_be64),
        H.limit_suffix(B.be64(high, low), payload, n,
          H.limit_of_bytes_equal(bs, B.concatenate(B.be64(high, low), payload), n, factoring_be64, limit)),
        rest_valid,
        G.record_accepted_extracts_all_os_fields(payload, cpost, tpost, q, v, rest_valid,
          (%fits : {R.machine(R.execute(payload,
            R.Frame{cpost, tpost, C.open_checked(_, C.CountsRecord{}, q, C.Root{})})) == C.DecodedReady{v} : C.Machine}
            ready)))

def prepare_tag(tag: Nat, +n: Nat, +b: U32, +bs: List<&2, U32>,
  +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  equal: {U32.to_nat(b) == tag : Nat},
  limit: {Nat.is_le(B.length(bs), n) == True{} : Bool},
  all_valid: {B.octets_all_valid(bs) == True{} : Bool},
  +ready: {R.machine(R.execute(Con{b, bs}, R.Frame{body, ceiling, C.Tag{C.Root{}}})) == C.DecodedReady{v} : C.Machine}) ->
  Branch<Con{b, bs}, v, n>:
  match tag:
    case 0n:
      +byte = T.u32_to_nat_injective(b, 0, equal)
      %Equal.sym(U32, b, 0, byte) : Branch<Con{_, bs}, v, n>
      Canonical{U.atom_combined_execution_trace(U.Absence{}, bs, body, ceiling, v,
        Rz.execution_ready_has_execution_trace_accepted(Con{0, bs}, body, ceiling, C.Tag{C.Root{}}, v,
          (%byte : {R.machine(R.execute(Con{_, bs}, R.Frame{body, ceiling, C.Tag{C.Root{}}})) == C.DecodedReady{v} : C.Machine}
            ready)))}
    case 1n:
      +byte = T.u32_to_nat_injective(b, 1, equal)
      %Equal.sym(U32, b, 1, byte) : Branch<Con{_, bs}, v, n>
      Canonical{U.atom_combined_execution_trace(U.Boolean{False{}}, bs, body, ceiling, v,
        Rz.execution_ready_has_execution_trace_accepted(Con{1, bs}, body, ceiling, C.Tag{C.Root{}}, v,
          (%byte : {R.machine(R.execute(Con{_, bs}, R.Frame{body, ceiling, C.Tag{C.Root{}}})) == C.DecodedReady{v} : C.Machine}
            ready)))}
    case 2n:
      +byte = T.u32_to_nat_injective(b, 2, equal)
      %Equal.sym(U32, b, 2, byte) : Branch<Con{_, bs}, v, n>
      Canonical{U.atom_combined_execution_trace(U.Boolean{True{}}, bs, body, ceiling, v,
        Rz.execution_ready_has_execution_trace_accepted(Con{2, bs}, body, ceiling, C.Tag{C.Root{}}, v,
          (%byte : {R.machine(R.execute(Con{_, bs}, R.Frame{body, ceiling, C.Tag{C.Root{}}})) == C.DecodedReady{v} : C.Machine}
            ready)))}
    case 3n:
      +byte = T.u32_to_nat_injective(b, 3, equal)
      %Equal.sym(U32, b, 3, byte) : Branch<Con{_, bs}, v, n>
      Canonical{Rz.integer_combined_execution_real_and_canonical(bs, C.decrease64(body), C.decrease64(ceiling), v, all_valid,
        (%byte : {R.machine(R.execute(Con{_, bs}, R.Frame{body, ceiling, C.Tag{C.Root{}}})) == C.DecodedReady{v} : C.Machine}
          ready))}
    case 4n:
      +byte = T.u32_to_nat_injective(b, 4, equal)
      %Equal.sym(U32, b, 4, byte) : Branch<Con{_, bs}, v, n>
      Canonical{Rz.text_combined_execution_real_and_canonical(bs, C.decrease64(body), C.decrease64(ceiling), v,
        Rz.execution_root_accepts_guarantees_value_valid(Con{b, bs}, body, ceiling, v, ready), all_valid,
        (%byte : {R.machine(R.execute(Con{_, bs}, R.Frame{body, ceiling, C.Tag{C.Root{}}})) == C.DecodedReady{v} : C.Machine}
          ready))}
    case 5n:
      +byte = T.u32_to_nat_injective(b, 5, equal)
      %Equal.sym(U32, b, 5, byte) : Branch<Con{_, bs}, v, n>
      prepare_list_extracted(n, bs, C.decrease64(body), C.decrease64(ceiling), v, limit,
        W.word_accepts_extracts_be64_and_execution_remaining(bs, C.CountsList{}, C.Root{},
          C.decrease64(body), C.decrease64(ceiling), v, all_valid,
          (%byte : {R.machine(R.execute(Con{_, bs}, R.Frame{body, ceiling, C.Tag{C.Root{}}})) == C.DecodedReady{v} : C.Machine}
            ready)))
    case 6n:
      +byte = T.u32_to_nat_injective(b, 6, equal)
      %Equal.sym(U32, b, 6, byte) : Branch<Con{_, bs}, v, n>
      prepare_record_extracted(n, bs, C.decrease64(body), C.decrease64(ceiling), v, limit,
        W.word_accepts_extracts_be64_and_execution_remaining(bs, C.CountsRecord{}, C.Root{},
          C.decrease64(body), C.decrease64(ceiling), v, all_valid,
          (%byte : {R.machine(R.execute(Con{_, bs}, R.Frame{body, ceiling, C.Tag{C.Root{}}})) == C.DecodedReady{v} : C.Machine}
            ready)))
    case 7n+p:
      L.ex_false(Branch<Con{b, bs}, v, n>, R.input_negative_decoded(v,
        Equal.trans(C.Outcome, C.Input{},
          C.traverse(bs, C.decrease64(body), C.decrease64(ceiling), C.Invalid{}), C.Decoded{v},
          Equal.sym(C.Outcome,
            C.traverse(bs, C.decrease64(body), C.decrease64(ceiling), C.Invalid{}), C.Input{},
            R.invalid_absorbs_all_suffix(bs, C.decrease64(body), C.decrease64(ceiling))),
          Rz.execution_ready_has_execution_trace_accepted(bs, C.decrease64(body), C.decrease64(ceiling), C.Invalid{}, v,
            (%equal : {R.machine(R.execute(bs,
              R.Frame{C.decrease64(body), C.decrease64(ceiling), C.read_tag(_, C.Root{})})) == C.DecodedReady{v} : C.Machine}
              ready)))))

# n is the predecessor of the root upper bound. Every extracted child receives
# that same n, including when the payload is empty.
law prepare_root:
  for +n: Nat
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for -v: D.Value
  for limit: {Nat.is_le(B.length(bs), 1n+n) == True{} : Bool}
  for all_valid: {B.octets_all_valid(bs) == True{} : Bool}
  for ready: {R.machine(R.execute(bs, R.Frame{body, ceiling, C.Tag{C.Root{}}})) == C.DecodedReady{v} : C.Machine}
  Branch<bs, v, n>
def prepare_root(n, bs, body, ceiling, v, limit, all_valid, ready):
  match bs:
    case Nil{}:
      L.ex_false(Branch<Nil{}, v, n>, A.tag_negative_and_ready(C.Root{}, v, ready))
    case Con{+b, +t}:
      prepare_tag(U32.to_nat(b), n, b, t, body, ceiling, v, {==}, limit,
        F.and_boolean_right(U32.is_le(b, 255), B.octets_all_valid(t), all_valid), ready)
