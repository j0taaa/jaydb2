# The outer record follows the private ABI order. Its child values are canonical.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../src/Codec.bend as Codec
import ../src/Remote.bend as Remote
import ./CodecCounters.bend as Counters
import ./Foundations.bend as F
import ./WireTheorems.bend as Wire

type Envelope is Data:
  ResultOnly{result: String}
  ResultWith{result: String, field: String, value: D.Value}

def fields(a: Envelope) -> List<&2, D.Field>:
  match a:
    case ResultOnly{r}: [D.Field{"result", D.VText{r}}]
    case ResultWith{r, n, v}: [D.Field{"result", D.VText{r}}, D.Field{n, v}]

def encode(a: Envelope) -> Maybe<&2, List<&2, U32>>:
  P.finalize(Remote.fields(fields(a)))

def flattened(a: Envelope) -> D.Value:
  match a:
    case ResultOnly{r}: D.VList{D.VText{"result"}, D.VList{D.VText{r}, D.VListEmpty{}}}
    case ResultWith{r, n, v}:
      D.VList{D.VText{"result"}, D.VList{D.VText{r}, D.VList{D.VText{n}, D.VList{v, D.VListEmpty{}}}}}

def NamesValid(a: Envelope) -> Type:
  match a:
    case ResultOnly{r}: {D.unicode_valid(r) == True{} : Bool}
    case ResultWith{r, n, v}:
      {D.unicode_valid(r) == True{} : Bool} & {D.unicode_valid(n) == True{} : Bool}

def reframe_encoded(bytes: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match bytes:
    case Some{bs}: Remote.answer_payload(bs)
    case None{}: None{}

def text_partial(bytes: Maybe<&2, List<&2, U32>>) ->
  {P.finalize(P.atom_optional(bytes)) == bytes : Maybe<&2, List<&2, U32>>}:
  match bytes:
    case None{}: {==}
    case Some{bs}: {==}

def flat_one(result: Maybe<&2, List<&2, U32>>) -> P.Partial:
  P.list_cases(P.text("result"), P.list_cases(result, P.ListFrame{0n, Nil{}}))

def record_one(result: Maybe<&2, List<&2, U32>>) -> P.Partial:
  P.record_cases(P.text("result"), result, P.Record{0n, Nil{}})

def flat_two(result: Maybe<&2, List<&2, U32>>, name: Maybe<&2, List<&2, U32>>,
  value: Maybe<&2, List<&2, U32>>) -> P.Partial:
  P.list_cases(P.text("result"), P.list_cases(result,
    P.list_cases(name, P.list_cases(value, P.ListFrame{0n, Nil{}}))))

def record_two(result: Maybe<&2, List<&2, U32>>, name: Maybe<&2, List<&2, U32>>,
  value: Maybe<&2, List<&2, U32>>) -> P.Partial:
  P.record_cases(P.text("result"), result, P.record_cases(name, value, P.Record{0n, Nil{}}))

def one_header(result: Maybe<&2, List<&2, U32>>) ->
  {P.finalize(flat_one(result)) == reframe_encoded(P.finalize(record_one(result))) : Maybe<&2, List<&2, U32>>}:
  match result:
    case None{}: {==}
    case Some{bs}: {==}

def two_header(ok: Bool, result: Maybe<&2, List<&2, U32>>, name: Maybe<&2, List<&2, U32>>,
  value: Maybe<&2, List<&2, U32>>) ->
  {P.encode_cases((ok && True{}) && True{}, P.finalize(flat_two(result, name, value))) ==
    reframe_encoded(P.finalize(record_two(result, name, P.encode_cases(ok, value)))) : Maybe<&2, List<&2, U32>>}:
  match ok result name value:
    case False{} None{} _ _: {==}
    case False{} Some{_} None{} _: {==}
    case False{} Some{_} Some{_} _: {==}
    case True{} None{} _ _: {==}
    case True{} Some{_} None{} _: {==}
    case True{} Some{_} Some{_} None{}: {==}
    case True{} Some{_} Some{_} Some{_}: {==}

law reframe_is_canonical_list_encoding:
  for +a: Envelope
  for names: NamesValid(a)
  {P.encode(flattened(a)) == reframe_encoded(encode(a)) : Maybe<&2, List<&2, U32>>}
def reframe_is_canonical_list_encoding(a, names):
  match a:
    case ResultOnly{+r}:
      %Equal.sym(Bool, D.unicode_valid(r), True{}, names) : {P.encode_cases((_ && True{}) && True{}, P.finalize(flat_one(P.finalize(P.atom_optional(P.text(r)))))) ==
        reframe_encoded(P.finalize(record_one(P.encode_cases(_, P.finalize(P.atom_optional(P.text(r))))))) : Maybe<&2, List<&2, U32>>}
      %Equal.sym(Maybe<&2, List<&2, U32>>, P.finalize(P.atom_optional(P.text(r))),
        P.text(r), text_partial(P.text(r))) : {P.finalize(flat_one(_)) == reframe_encoded(P.finalize(record_one(_))) : Maybe<&2, List<&2, U32>>}
      one_header(P.text(r))
    case ResultWith{+r, +n, +v}:
      match names:
        case (rv, nv):
          %Equal.sym(Bool, D.unicode_valid(r), True{}, rv) : {P.encode_cases((_ && True{}) && ((D.unicode_valid(n) && True{}) && ((D.value_valid(v) && True{}) && True{})),
              P.finalize(flat_two(P.finalize(P.atom_optional(P.text(r))), P.finalize(P.atom_optional(P.text(n))), P.finalize(P.encode_partial(v))))) ==
            reframe_encoded(P.finalize(record_two(P.encode_cases(_, P.finalize(P.atom_optional(P.text(r)))),
              P.text(n), P.encode(v)))) : Maybe<&2, List<&2, U32>>}
          %Equal.sym(Bool, D.unicode_valid(n), True{}, nv) : {P.encode_cases((_ && True{}) && ((D.value_valid(v) && True{}) && True{}),
              P.finalize(flat_two(P.finalize(P.atom_optional(P.text(r))), P.finalize(P.atom_optional(P.text(n))), P.finalize(P.encode_partial(v))))) ==
            reframe_encoded(P.finalize(record_two(P.finalize(P.atom_optional(P.text(r))), P.text(n), P.encode(v)))) : Maybe<&2, List<&2, U32>>}
          %Equal.sym(Maybe<&2, List<&2, U32>>, P.finalize(P.atom_optional(P.text(r))),
        P.text(r), text_partial(P.text(r))) : {P.encode_cases((D.value_valid(v) && True{}) && True{},
              P.finalize(flat_two(_, P.finalize(P.atom_optional(P.text(n))), P.finalize(P.encode_partial(v))))) ==
            reframe_encoded(P.finalize(record_two(_, P.text(n), P.encode(v)))) : Maybe<&2, List<&2, U32>>}
          %Equal.sym(Maybe<&2, List<&2, U32>>, P.finalize(P.atom_optional(P.text(n))),
        P.text(n), text_partial(P.text(n))) : {P.encode_cases((D.value_valid(v) && True{}) && True{},
              P.finalize(flat_two(P.text(r), _, P.finalize(P.encode_partial(v))))) ==
            reframe_encoded(P.finalize(record_two(P.text(r), P.text(n), P.encode(v)))) : Maybe<&2, List<&2, U32>>}
          two_header(D.value_valid(v), P.text(r), P.text(n), P.finalize(P.encode_partial(v)))

def ceiling() -> B.Number64:
  B.Number64{4294967295, 4294967295}

def bit_below_max(bit: Bool, tail: Cmp, below: {Cmp.is_le(tail) == True{} : Bool}) ->
  {Cmp.is_le(Word.cmp.fin(bit, True{}, tail)) == True{} : Bool}:
  match bit tail:
    case _ LT{}: {==}
    case False{} EQ{}: {==}
    case True{} EQ{}: {==}
    case _ GT{}: F.absurd_boolean({Cmp.is_le(Word.cmp.fin(bit, True{}, GT{})) == True{} : Bool}, below)

law word_below_max:
  for n: Nat
  for w: Word(n)
  {Cmp.is_le(Word.cmp(n, w, Counters.maximum(n))) == True{} : Bool}
def word_below_max(n, w):
  match n:
    case 0n: {==}
    case 1n+ +p:
      match w:
        case WCon{b, +tail}:
          bit_below_max(b, Word.cmp(p, tail, Counters.maximum(p)), word_below_max(p, tail))

def below_max_pair(high: Cmp, low: Cmp, high_below: {Cmp.is_le(high) == True{} : Bool},
  low_below: {Cmp.is_le(low) == True{} : Bool}) ->
  {(Cmp.is_lt(high) || (Cmp.is_eq(high) && Cmp.is_le(low))) == True{} : Bool}:
  match high:
    case LT{}: {==}
    case EQ{}: low_below
    case GT{}: F.absurd_boolean({False{} == True{} : Bool}, high_below)

law answer_body_fits_ceiling:
  for +body: B.Number64
  {Codec.less_equal64(body, ceiling()) == True{} : Bool}
def answer_body_fits_ceiling(body):
  match body:
    case B.Number64{U32{+high}, U32{+low}}:
      below_max_pair(Word.cmp(32n, high, Counters.maximum(32n)), Word.cmp(32n, low, Counters.maximum(32n)),
        word_below_max(32n, high), word_below_max(32n, low))

type Reframed<-bytes: List<&2, U32>> is Type:
  Reframed{payload: List<&2, U32>,
    exact: {Remote.answer_payload(bytes) == Some{payload} : Maybe<&2, List<&2, U32>>},
    same_length: {B.length(payload) == B.length(bytes) : Nat}}

def EncodedHeader(bytes: Maybe<&2, List<&2, U32>>) -> Type:
  match bytes:
    case None{}: Unit
    case Some{bs}: Reframed<bs>

def result_field_bytes() -> List<&2, U32>:
  Con{4, B.concatenate(B.be64(0, 6), B.utf8("result"))}

def header_one(result: Maybe<&2, List<&2, U32>>) -> EncodedHeader(P.finalize(record_one(result))):
  match result:
    case None{}: Unit{}
    case Some{tail}: Reframed{Con{5, B.concatenate(B.be64(0, 2), B.concatenate(result_field_bytes(), B.concatenate(tail, Nil{})))}, {==}, {==}}

def header_two(result: Maybe<&2, List<&2, U32>>, name: Maybe<&2, List<&2, U32>>,
  value: Maybe<&2, List<&2, U32>>) -> EncodedHeader(P.finalize(record_two(result, name, value))):
  match result name value:
    case None{} _ _: Unit{}
    case Some{_} None{} _: Unit{}
    case Some{_} Some{_} None{}: Unit{}
    case Some{r} Some{n} Some{v}:
      Reframed{Con{5, B.concatenate(B.be64(0, 4), B.concatenate(result_field_bytes(),
        B.concatenate(r, B.concatenate(n, B.concatenate(v, Nil{})))))}, {==}, {==}}

def encoded_header(a: Envelope) -> EncodedHeader(encode(a)):
  match a:
    case ResultOnly{r}: header_one(P.encode(D.VText{r}))
    case ResultWith{r, n, v}: header_two(P.encode(D.VText{r}), P.text(n), P.encode(v))

law encoded_answer_reframes:
  for +a: Envelope
  for +bytes: List<&2, U32>
  for encoded: {encode(a) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  Reframed<bytes>
def encoded_answer_reframes(a, bytes, encoded):
  %encoded : EncodedHeader(_)
  encoded_header(a)

def roundtrip_reframed(+a: Envelope, names: NamesValid(a), +bytes: List<&2, U32>, +body: B.Number64,
  encoded: {encode(a) == Some{bytes} : Maybe<&2, List<&2, U32>>},
  measured: {B.nat64(B.length(bytes)) == Some{body} : Maybe<&2, B.Number64>},
  fits: {Codec.less_equal64(body, ceiling()) == True{} : Bool}, header: Reframed<bytes>) ->
  {Remote.answer(bytes) == Codec.Decoded{flattened(a)} : Codec.Outcome}:
  match header:
    case Reframed{+payload, +reframed, same_length}:
      canonical = Equal.trans(Maybe<&2, List<&2, U32>>, P.encode(flattened(a)),
        reframe_encoded(encode(a)), Some{payload}, reframe_is_canonical_list_encoding(a, names),
        Equal.trans(Maybe<&2, List<&2, U32>>, reframe_encoded(encode(a)), Remote.answer_payload(bytes), Some{payload},
          Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, List<&2, U32>>, x => reframe_encoded(x),
            encode(a), Some{bytes}, encoded), reframed))
      %Equal.sym(Maybe<&2, List<&2, U32>>, Remote.answer_payload(bytes), Some{payload}, reframed) :
        {Remote.decode_answer(_) == Codec.Decoded{flattened(a)} : Codec.Outcome}
      Wire.codec_roundtrip()(flattened(a), payload, body, ceiling(), canonical,
        Equal.trans(Maybe<&2, B.Number64>, B.nat64(B.length(payload)), B.nat64(B.length(bytes)), Some{body},
          Equal.cong(Nat, Maybe<&2, B.Number64>, n => B.nat64(n), B.length(payload), B.length(bytes), same_length),
          measured), fits)

law answer_encoding_roundtrip:
  for +a: Envelope
  for names: NamesValid(a)
  for +bytes: List<&2, U32>
  for +body: B.Number64
  for +encoded: {encode(a) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  for measured: {B.nat64(B.length(bytes)) == Some{body} : Maybe<&2, B.Number64>}
  {Remote.answer(bytes) == Codec.Decoded{flattened(a)} : Codec.Outcome}
def answer_encoding_roundtrip(a, names, bytes, body, encoded, measured):
  roundtrip_reframed(a, names, bytes, body, encoded, measured, answer_body_fits_ceiling(body),
    encoded_answer_reframes(a, bytes, encoded))
