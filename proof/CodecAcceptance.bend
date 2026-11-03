# General SOUNDNESS: actually accepted bytes are exactly P.encode(v).
# Recursion is lexicographic in (length, phase, children, fields).
# The Nat index is mathematical length: no new parser quota.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecTrace.bend as R
import ./CodecArities.bend as A
import ./CodecLimitsSequences.bend as S
import ./CodecAssembly.bend as M
import ./CodecAssemblyClosed.bend as MF
import ./CodecAssemblyOrder.bend as MO
import ./CodecRelax.bend as Relax
import ./CodecAcceptanceWord.bend as W
import ./CodecAcceptanceChildren.bend as H
import ./CodecAcceptanceRecord.bend as G
import ./CodecAcceptanceInduction.bend as I
import ./CodecAcceptancePreparation.bend as Q

def encoding_of_record_closed(+xs: List<&2, S.FieldSegmented>, +q: B.Number64, -v: D.Value,
  closed: L.E<{B.nat64(S.count_fields(xs)) == Some{q} : Maybe<&2, B.Number64>},
    L.E<A.FieldsOrdered(S.fields(xs), ""), P.Encoding(v, M.prefix(6, q, S.bytes_fields(xs)))>>) ->
  P.Encoding(v, M.prefix(6, q, S.bytes_fields(xs))):
  match closed:
    case L.Both{measure, L.Both{order, encoded}}:
      encoded

def close_branch(+n: Nat, +bs: List<&2, U32>, -v: D.Value,
  branch: Q.Branch<bs, v, n>,
  values: @xs: List<&2, S.ValueSegmented> -> H.ChildrenRead(xs, n) ->
    {B.octets_all_valid(S.bytes_values(xs)) == True{} : Bool} -> S.ValuesCanonical(xs),
  fields: @ys: List<&2, S.FieldSegmented> -> G.FieldsRead(ys, n) ->
    {B.octets_all_valid(S.bytes_fields(ys)) == True{} : Bool} -> S.FieldsCanonical(ys)) -> P.Encoding(v, bs):
  match branch:
    case Q.Canonical{encoded}:
      encoded
    case Q.ListFrame{+q, +xs, bytes, delivery, children, octets}:
      F.combined_pair(P.Encoding(v, bs),
        {B.nat64(S.count_values(xs)) == Some{q} : Maybe<&2, B.Number64>},
        P.Encoding(v, M.prefix(5, q, S.bytes_values(xs))),
        MF.list_closed_has_measure_and_encoding_canonical(xs, q, v, values(xs, children, octets), delivery),
        measure => encoded =>
          (%Equal.sym(List<&2, U32>, bs, M.prefix(5, q, S.bytes_values(xs)), bytes) : P.Encoding(v, _)
            encoded))
    case Q.Record{+q, +xs, bytes, delivery, children, octets}:
      %Equal.sym(List<&2, U32>, bs, M.prefix(6, q, S.bytes_fields(xs)), bytes) : P.Encoding(v, _)
      encoding_of_record_closed(xs, q, v,
        MO.record_closed_extracts_measure_order_and_encoding_canonical(xs, q, v, fields(xs, children, octets), delivery))

# Phase 0 resolves ONE value; phase 1 resolves list children;
# phase 2 resolves field values whose names have already been inverted.
# The child phase only calls phase 0 with the same n, which is below the
# length admitted by the parent value. Every tail decreases structurally.
law resolve:
  for +n: Nat
  for phase: Nat
  for +xs: List<&2, S.ValueSegmented>
  for +ys: List<&2, S.FieldSegmented>
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +v: D.Value
  for proof: I.Obligation(n, phase, xs, ys, bs, body, ceiling, v)
  I.Conclusion(phase, xs, ys, bs, v)
def resolve(n, phase, xs, ys, bs, body, ceiling, v, proof):
  match n phase xs ys bs:
    case 0n 0n _ _ Nil{}:
      match proof:
        case L.Both{limit, L.Both{octets, ready}}:
          L.ex_false(P.Encoding(v, Nil{}), A.tag_negative_and_ready(C.Root{}, v, ready))
    case 0n 0n _ _ Con{b, t}:
      match proof:
        case L.Both{limit, rest}:
          F.absurd_boolean(P.Encoding(v, bs), limit)
    case 1n+p 0n _ _ _:
      match proof:
        case L.Both{limit, L.Both{octets, ready}}:
          +less = p
          close_branch(less, bs, v, Q.prepare_root(less, bs, body, ceiling, v, limit, octets, ready),
            children => read => all_valid =>
              resolve(less, 1n, children, Nil{}, Nil{}, B.Number64{0, 0}, B.Number64{0, 0}, D.VAbsent{}, L.Both{read, all_valid}),
            fields => read => all_valid =>
              resolve(less, 2n, Nil{}, fields, Nil{}, B.Number64{0, 0}, B.Number64{0, 0}, D.VAbsent{}, L.Both{read, all_valid}))
    case _ 1n Nil{} _ _:
      Unit{}
    case _ 1n Con{S.ValueSegmented{+h, +hb}, +rest} _ _:
      match proof:
        case L.Both{L.Both{H.ChildRead{+hc, +ht, +outside, local, limit}, tail}, all_valid}:
          F.combined_pair(S.ValuesCanonical(xs),
            {B.octets_all_valid(hb) == True{} : Bool}, {B.octets_all_valid(S.bytes_values(rest)) == True{} : Bool},
            W.separate_octets_all_valid(hb, S.bytes_values(rest), all_valid),
            head_is_valid => tail_is_valid => L.Both{
              resolve(n, 0n, Nil{}, Nil{}, hb, hc, ht, h,
                L.Both{limit, L.Both{head_is_valid,
                  Relax.execution_local_accepts_continues_accepts_without_stack_external(hb, outside, hc, ht, C.Tag{C.Root{}}, h, local)}}),
              resolve(n, 1n, rest, ys, bs, body, ceiling, v, L.Both{tail, tail_is_valid})})
    case _ 2n _ Nil{} _:
      Unit{}
    case _ 2n _ Con{S.FieldSegmented{+name, +h, +nb, +hb}, +rest} _:
      match proof:
        case L.Both{L.Both{name_valid, L.Both{name_canonical, L.Both{H.ChildRead{+hc, +ht, +outside, local, limit}, tail}}}, all_valid}:
          F.combined_pair(S.FieldsCanonical(ys),
            {B.octets_all_valid(B.concatenate(nb, hb)) == True{} : Bool}, {B.octets_all_valid(S.bytes_fields(rest)) == True{} : Bool},
            W.separate_octets_all_valid(B.concatenate(nb, hb), S.bytes_fields(rest), all_valid),
            pair_valid => tail_is_valid =>
              F.combined_pair(S.FieldsCanonical(ys), {B.octets_all_valid(nb) == True{} : Bool}, {B.octets_all_valid(hb) == True{} : Bool},
                W.separate_octets_all_valid(nb, hb, pair_valid),
                bytes_name => bytes_value => L.Both{name_valid, L.Both{name_canonical, L.Both{
                  resolve(n, 0n, Nil{}, Nil{}, hb, hc, ht, h,
                    L.Both{limit, L.Both{bytes_value,
                      Relax.execution_local_accepts_continues_accepts_without_stack_external(hb, outside, hc, ht, C.Tag{C.Root{}}, h, local)}}),
                  resolve(n, 2n, xs, rest, bs, body, ceiling, v, L.Both{tail, tail_is_valid})}}}))
    case _ 3n+p _ _ _:
      Unit{}

law all_execution_root_ready_reconstructs_to_encoding_original:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +v: D.Value
  for all_valid: {B.octets_all_valid(bs) == True{} : Bool}
  for ready: {R.machine(R.execute(bs, R.Frame{body, ceiling, C.Tag{C.Root{}}})) == C.DecodedReady{v} : C.Machine}
  P.Encoding(v, bs)
def all_execution_root_ready_reconstructs_to_encoding_original(bs, body, ceiling, v, all_valid, ready):
  resolve(B.length(bs), 0n, Nil{}, Nil{}, bs, body, ceiling, v,
    L.Both{S.limit_reflexive(B.length(bs)), L.Both{all_valid, ready}})

def accept_input_checked(+bs: List<&2, U32>, +ceiling: B.Number64, +v: D.Value,
  input: R.InputChecked<B.nat64(B.length(bs)), bs, ceiling, v>) -> P.Encoding(v, bs):
  match input:
    case R.Checked{+body, measure, fits, octets, execution_trace}:
      all_execution_root_ready_reconstructs_to_encoding_original(bs, body, ceiling, v, octets,
        R.execution_trace_accepted_terminates_ready(bs, R.Frame{body, ceiling, C.Tag{C.Root{}}}, v, execution_trace))

# Sole premise: the ACCEPTANCE equality of the actual public API.
# No Environment, child canonicity, segmentation or count is supplied.
law all_acceptance_publish_has_encoding_canonical:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for +v: D.Value
  for accepted: {C.decode(bs, ceiling) == C.Decoded{v} : C.Outcome}
  P.Encoding(v, bs)
def all_acceptance_publish_has_encoding_canonical(bs, ceiling, v, accepted):
  accept_input_checked(bs, ceiling, v,
    R.acceptance_requires_body_representable_octets_and_limit(bs, ceiling, v, accepted))
