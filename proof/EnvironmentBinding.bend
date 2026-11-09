# Exact environment descriptor framing. This proves injectivity of the bytes,
# not collision resistance of the diagnostic environment hash. Native source
# enumeration and file IO must refine these same name/content frames.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../src/Transport.bend as T
import ./Transport.bend as Q
import ./Foundations.bend as F
import ../src/Codec.bend as Codec
import ./CodecUTF8.bend as Text
import ./CodecUTF8Inverse.bend as Utf8

type Entry is Data:
  Entry{name: List<&2, U32>, content: List<&2, U32>}

type Sized is Data:
  Sized{entry: Entry, name_size: B.Number64, content_size: B.Number64}

def first(p: T.Parts) -> List<&2, U32>:
  match p:
    case T.Parts{a, b}: a

def second(p: T.Parts) -> List<&2, U32>:
  match p:
    case T.Parts{a, b}: b

def frame(data: List<&2, U32>, size: B.Number64, suffix: List<&2, U32>) -> List<&2, U32>:
  match size:
    case B.Number64{hi, lo}: B.concatenate(B.be64(hi, lo), B.concatenate(data, suffix))

law frame_recovers_payload_and_exact_suffix:
  for +data: List<&2, U32>
  for +size: B.Number64
  for +suffix: List<&2, U32>
  for measured: {B.nat64(B.length(data)) == Some{size} : Maybe<&2, B.Number64>}
  {T.header(frame(data, size, suffix)) == Some{T.Parts{data, suffix}} : Maybe<&2, T.Parts>}
def frame_recovers_payload_and_exact_suffix(data, size, suffix, measured):
  match size:
    case B.Number64{+hi, +lo}:
      Equal.trans(Maybe<&2, T.Parts>, T.header(frame(data, B.Number64{hi, lo}, suffix)),
        T.cut(B.concatenate(data, suffix), B.Number64{hi, lo}, Nil{}), Some{T.Parts{data, suffix}},
        Q.header_inverts_be64(hi, lo, B.concatenate(data, suffix)),
        Q.cut_preserves_exactly_os_two_blocks(data, suffix, B.Number64{hi, lo}, measured))

law equal_frames_have_equal_parts:
  for +a: List<&2, U32>
  for +na: B.Number64
  for +sa: List<&2, U32>
  for +b: List<&2, U32>
  for +nb: B.Number64
  for +sb: List<&2, U32>
  for ma: {B.nat64(B.length(a)) == Some{na} : Maybe<&2, B.Number64>}
  for mb: {B.nat64(B.length(b)) == Some{nb} : Maybe<&2, B.Number64>}
  for equal: {frame(a, na, sa) == frame(b, nb, sb) : List<&2, U32>}
  {T.Parts{a, sa} == T.Parts{b, sb} : T.Parts}
def equal_frames_have_equal_parts(a, na, sa, b, nb, sb, ma, mb, equal):
  F.some_injective(T.Parts, T.Parts{a, sa}, T.Parts{b, sb},
    Equal.trans(Maybe<&2, T.Parts>, Some{T.Parts{a, sa}}, T.header(frame(a, na, sa)), Some{T.Parts{b, sb}},
      Equal.sym(Maybe<&2, T.Parts>, T.header(frame(a, na, sa)), Some{T.Parts{a, sa}},
        frame_recovers_payload_and_exact_suffix(a, na, sa, ma)),
      Equal.trans(Maybe<&2, T.Parts>, T.header(frame(a, na, sa)), T.header(frame(b, nb, sb)), Some{T.Parts{b, sb}},
        Equal.cong(List<&2, U32>, Maybe<&2, T.Parts>, T.header, frame(a, na, sa), frame(b, nb, sb), equal),
        frame_recovers_payload_and_exact_suffix(b, nb, sb, mb))))

def bytes(xs: List<&2, Sized>) -> List<&2, U32>:
  match xs:
    case Nil{}: Nil{}
    case Con{Sized{Entry{name, content}, ns, cs}, tail}:
      frame(name, ns, frame(content, cs, bytes(tail)))

def entries(xs: List<&2, Sized>) -> List<&2, Entry>:
  match xs:
    case Nil{}: Nil{}
    case Con{Sized{e, ns, cs}, tail}: Con{e, entries(tail)}

def Measured(xs: List<&2, Sized>) -> Type:
  match xs:
    case Nil{}: Unit
    case Con{Sized{Entry{name, content}, ns, cs}, tail}:
      L.E<{B.nat64(B.length(name)) == Some{ns} : Maybe<&2, B.Number64>},
        L.E<{B.nat64(B.length(content)) == Some{cs} : Maybe<&2, B.Number64>}, Measured(tail)>>

law framed_descriptor_is_injective_in_all_names_contents_and_order:
  for +xs: List<&2, Sized>
  for +ys: List<&2, Sized>
  for mx: Measured(xs)
  for my: Measured(ys)
  for equal: {bytes(xs) == bytes(ys) : List<&2, U32>}
  {entries(xs) == entries(ys) : List<&2, Entry>}
def framed_descriptor_is_injective_in_all_names_contents_and_order(xs, ys, mx, my, equal):
  match xs ys:
    case Nil{} Nil{}: {==}
    case Nil{} Con{Sized{Entry{+name, +content}, +ns, +cs}, +tail}:
      match my:
        case L.Both{mn, rest}:
          +impossible = Equal.trans(Maybe<&2, T.Parts>, None{}, T.header(bytes(Con{Sized{Entry{name, content}, ns, cs}, tail})),
            Some{T.Parts{name, frame(content, cs, bytes(tail))}},
            Equal.cong(List<&2, U32>, Maybe<&2, T.Parts>, T.header, Nil{}, bytes(Con{Sized{Entry{name, content}, ns, cs}, tail}), equal),
            frame_recovers_payload_and_exact_suffix(name, ns, frame(content, cs, bytes(tail)), mn))
          L.ex_false({Nil{} == entries(Con{Sized{Entry{name, content}, ns, cs}, tail}) : List<&2, Entry>},
            F.none_negative_some(T.Parts, T.Parts{name, frame(content, cs, bytes(tail))}, impossible))
    case Con{Sized{Entry{+name, +content}, +ns, +cs}, +tail} Nil{}:
      match mx:
        case L.Both{mn, rest}:
          +impossible = Equal.trans(Maybe<&2, T.Parts>, None{}, T.header(bytes(Con{Sized{Entry{name, content}, ns, cs}, tail})),
            Some{T.Parts{name, frame(content, cs, bytes(tail))}},
            Equal.cong(List<&2, U32>, Maybe<&2, T.Parts>, T.header, Nil{}, bytes(Con{Sized{Entry{name, content}, ns, cs}, tail}),
              Equal.sym(List<&2, U32>, bytes(Con{Sized{Entry{name, content}, ns, cs}, tail}), Nil{}, equal)),
            frame_recovers_payload_and_exact_suffix(name, ns, frame(content, cs, bytes(tail)), mn))
          L.ex_false({entries(Con{Sized{Entry{name, content}, ns, cs}, tail}) == Nil{} : List<&2, Entry>},
            F.none_negative_some(T.Parts, T.Parts{name, frame(content, cs, bytes(tail))}, impossible))
    case Con{Sized{Entry{+xn, +xc}, +xns, +xcs}, +xt} Con{Sized{Entry{+yn, +yc}, +yns, +ycs}, +yt}:
      match mx my:
        case L.Both{mxn, L.Both{mxc, mxt}} L.Both{myn, L.Both{myc, myt}}:
          +names = equal_frames_have_equal_parts(xn, xns, frame(xc, xcs, bytes(xt)),
            yn, yns, frame(yc, ycs, bytes(yt)), mxn, myn, equal)
          +name_equal = Equal.cong(T.Parts, List<&2, U32>, first,
            T.Parts{xn, frame(xc, xcs, bytes(xt))}, T.Parts{yn, frame(yc, ycs, bytes(yt))}, names)
          +content_frames = Equal.cong(T.Parts, List<&2, U32>, second,
            T.Parts{xn, frame(xc, xcs, bytes(xt))}, T.Parts{yn, frame(yc, ycs, bytes(yt))}, names)
          +contents = equal_frames_have_equal_parts(xc, xcs, bytes(xt), yc, ycs, bytes(yt), mxc, myc, content_frames)
          +content_equal = Equal.cong(T.Parts, List<&2, U32>, first,
            T.Parts{xc, bytes(xt)}, T.Parts{yc, bytes(yt)}, contents)
          tail_equal = Equal.cong(T.Parts, List<&2, U32>, second,
            T.Parts{xc, bytes(xt)}, T.Parts{yc, bytes(yt)}, contents)
          %Equal.sym(List<&2, U32>, xn, yn, name_equal) :
            {Con{Entry{_, xc}, entries(xt)} == Con{Entry{yn, yc}, entries(yt)} : List<&2, Entry>}
          %Equal.sym(List<&2, U32>, xc, yc, content_equal) :
            {Con{Entry{yn, _}, entries(xt)} == Con{Entry{yn, yc}, entries(yt)} : List<&2, Entry>}
          Equal.cong(List<&2, Entry>, List<&2, Entry>, tail => Con{Entry{yn, yc}, tail}, entries(xt), entries(yt),
            framed_descriptor_is_injective_in_all_names_contents_and_order(xt, yt, mxt, myt, tail_equal))

def drop_head(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}: Nil{}
    case Con{h, t}: t

law cancel_shared_byte_prefix:
  for prefix: List<&2, U32>
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for equal: {B.concatenate(prefix, a) == B.concatenate(prefix, b) : List<&2, U32>}
  {a == b : List<&2, U32>}
def cancel_shared_byte_prefix(prefix, a, b, equal):
  match prefix:
    case Nil{}: equal
    case Con{+h, +tail}:
      cancel_shared_byte_prefix(tail, a, b,
        Equal.cong(List<&2, U32>, List<&2, U32>, drop_head,
          Con{h, B.concatenate(tail, a)}, Con{h, B.concatenate(tail, b)}, equal))

def descriptor(xs: List<&2, Sized>) -> List<&2, U32>:
  B.concatenate(B.utf8("jaydb2-environment-v1\n"), bytes(xs))

law exact_descriptors_bind_every_source_and_controller_byte:
  for +xs: List<&2, Sized>
  for +ys: List<&2, Sized>
  for mx: Measured(xs)
  for my: Measured(ys)
  for equal: {descriptor(xs) == descriptor(ys) : List<&2, U32>}
  {entries(xs) == entries(ys) : List<&2, Entry>}
def exact_descriptors_bind_every_source_and_controller_byte(xs, ys, mx, my, equal):
  framed_descriptor_is_injective_in_all_names_contents_and_order(xs, ys, mx, my,
    cancel_shared_byte_prefix(B.utf8("jaydb2-environment-v1\n"), bytes(xs), bytes(ys), equal))

# Text sources use strict UTF-8; their byte equality recovers equality of the
# original Unicode source, not just a normalized or replacement-decoded text.
def strict_text(bytes: List<&2, U32>) -> Maybe<&2, String>:
  Text.finalize_text(Text.traverse_text(bytes, Text.Reading{Codec.Start{}, ""}))

law equal_valid_utf8_source_bytes_have_identical_source_text:
  for +a: String
  for +b: String
  for va: {B.text_valid(a) == True{} : Bool}
  for vb: {B.text_valid(b) == True{} : Bool}
  for same: {B.utf8(a) == B.utf8(b) : List<&2, U32>}
  {a == b : String}
def equal_valid_utf8_source_bytes_have_identical_source_text(a, b, va, vb, same):
  F.some_injective(String, a, b,
    Equal.trans(Maybe<&2, String>, Some{a}, strict_text(B.utf8(a)), Some{b},
      Equal.sym(Maybe<&2, String>, strict_text(B.utf8(a)), Some{a}, Utf8.utf8_text_valid_decodes_exactly(a, va)),
      Equal.trans(Maybe<&2, String>, strict_text(B.utf8(a)), strict_text(B.utf8(b)), Some{b},
        Equal.cong(List<&2, U32>, Maybe<&2, String>, strict_text, B.utf8(a), B.utf8(b), same),
        Utf8.utf8_text_valid_decodes_exactly(b, vb))))
