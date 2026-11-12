# All-input refinement of fused validation/cutting, including malformed U32s.
import Base
import ../contract/Bytes.bend as B
import ../src/Codec.bend as C
import ../src/Transport.bend as T

def restore(acc: List<&2, U32>, parts: Maybe<&2, T.Parts>) -> Maybe<&2, T.Parts>:
  match parts:
    case None{}: None{}
    case Some{T.Parts{first, second}}: Some{T.Parts{T.invert(acc, first), second}}

law restore_accept:
  for ok: Bool
  for +acc: List<&2, U32>
  for +parts: Maybe<&2, T.Parts>
  {restore(acc, T.accept(ok, parts)) == T.accept(ok, restore(acc, parts)) : Maybe<&2, T.Parts>}
def restore_accept(ok, acc, parts):
  match ok:
    case False{}: {==}
    case True{}: {==}

law restore_prepend:
  for +h: U32
  for +acc: List<&2, U32>
  for parts: Maybe<&2, T.Parts>
  {restore(acc, T.prepend(h, parts)) == restore(Con{h, acc}, parts) : Maybe<&2, T.Parts>}
def restore_prepend(h, acc, parts):
  match parts:
    case None{}: {==}
    case Some{T.Parts{first, second}}: {==}

law accept_nested:
  for a: Bool
  for b: Bool
  for +parts: Maybe<&2, T.Parts>
  {T.accept(a, T.accept(b, parts)) == T.accept(a && b, parts) : Maybe<&2, T.Parts>}
def accept_nested(a, b, parts):
  match a:
    case False{}: {==}
    case True{}: {==}

law restore_empty:
  for parts: Maybe<&2, T.Parts>
  {restore(Nil{}, parts) == parts : Maybe<&2, T.Parts>}
def restore_empty(parts):
  match parts:
    case None{}: {==}
    case Some{T.Parts{first, second}}: {==}

law scan_empty:
  for zero: Bool
  for +acc: List<&2, U32>
  {restore(acc, T.accept(zero, Some{T.Parts{Nil{}, Nil{}}})) == T.empty(zero, acc) : Maybe<&2, T.Parts>}
def scan_empty(zero, acc):
  match zero:
    case False{}: {==}
    case True{}: {==}

law scan_step_refines:
  for zero: Bool
  for +h: U32
  for +t: List<&2, U32>
  for +count: B.Number64
  for +acc: List<&2, U32>
  for ih: {restore(Con{h, acc}, T.scan(t, C.decrease64(count))) ==
    T.accept(B.octets_all_valid(t), T.cut(t, C.decrease64(count), Con{h, acc})) : Maybe<&2, T.Parts>}
  {restore(acc, T.scan_step(zero, h, t, unit => T.scan(t, C.decrease64(count)))) ==
    T.accept(B.octets_all_valid(Con{h, t}), T.divert(zero,
      unit => Some{T.Parts{T.invert(acc, Nil{}), Con{h, t}}},
      unit => T.cut(t, C.decrease64(count), Con{h, acc}))) : Maybe<&2, T.Parts>}
def scan_step_refines(zero, h, t, count, acc, ih):
  match zero:
    case True{}:
      restore_accept(B.octets_all_valid(Con{h, t}), acc, Some{T.Parts{Nil{}, Con{h, t}}})
    case False{}:
      %Equal.sym(Maybe<&2, T.Parts>, restore(acc, T.accept(U32.is_le(h, 255), T.prepend(h, T.scan(t, C.decrease64(count))))),
        T.accept(U32.is_le(h, 255), restore(acc, T.prepend(h, T.scan(t, C.decrease64(count))))),
        restore_accept(U32.is_le(h, 255), acc, T.prepend(h, T.scan(t, C.decrease64(count))))) :
        {_ == T.accept(B.octets_all_valid(Con{h, t}), T.cut(t, C.decrease64(count), Con{h, acc})) : Maybe<&2, T.Parts>}
      %Equal.sym(Maybe<&2, T.Parts>, restore(acc, T.prepend(h, T.scan(t, C.decrease64(count)))),
        restore(Con{h, acc}, T.scan(t, C.decrease64(count))),
        restore_prepend(h, acc, T.scan(t, C.decrease64(count)))) :
        {T.accept(U32.is_le(h, 255), _) == T.accept(B.octets_all_valid(Con{h, t}), T.cut(t, C.decrease64(count), Con{h, acc})) : Maybe<&2, T.Parts>}
      %Equal.sym(Maybe<&2, T.Parts>, restore(Con{h, acc}, T.scan(t, C.decrease64(count))),
        T.accept(B.octets_all_valid(t), T.cut(t, C.decrease64(count), Con{h, acc})), ih) :
        {T.accept(U32.is_le(h, 255), _) == T.accept(B.octets_all_valid(Con{h, t}), T.cut(t, C.decrease64(count), Con{h, acc})) : Maybe<&2, T.Parts>}
      accept_nested(U32.is_le(h, 255), B.octets_all_valid(t), T.cut(t, C.decrease64(count), Con{h, acc}))

law scan_refines_cut:
  for +bytes: List<&2, U32>
  for +count: B.Number64
  for +acc: List<&2, U32>
  {restore(acc, T.scan(bytes, count)) == T.accept(B.octets_all_valid(bytes), T.cut(bytes, count, acc)) : Maybe<&2, T.Parts>}
def scan_refines_cut(bytes, count, acc):
  match bytes:
    case Nil{}: scan_empty(C.zero64(count), acc)
    case Con{+h, +t}:
      scan_step_refines(C.zero64(count), h, t, count, acc, scan_refines_cut(t, C.decrease64(count), Con{h, acc}))

law scan_without_accumulator:
  for +bytes: List<&2, U32>
  for +count: B.Number64
  {T.scan(bytes, count) == T.accept(B.octets_all_valid(bytes), T.cut(bytes, count, Nil{})) : Maybe<&2, T.Parts>}
def scan_without_accumulator(bytes, count):
  Equal.trans(Maybe<&2, T.Parts>, T.scan(bytes, count), restore(Nil{}, T.scan(bytes, count)),
    T.accept(B.octets_all_valid(bytes), T.cut(bytes, count, Nil{})),
    Equal.sym(Maybe<&2, T.Parts>, restore(Nil{}, T.scan(bytes, count)), T.scan(bytes, count), restore_empty(T.scan(bytes, count))),
    scan_refines_cut(bytes, count, Nil{}))

law validate_accept:
  for ok: Bool
  for +bytes: List<&2, U32>
  {T.validate(ok, bytes) == T.accept(ok, T.header(bytes)) : Maybe<&2, T.Parts>}
def validate_accept(ok, bytes):
  match ok:
    case False{}: {==}
    case True{}: {==}

law accept_none:
  for ok: Bool
  {T.accept(ok, None{}) == None{} : Maybe<&2, T.Parts>}
def accept_none(ok):
  match ok:
    case False{}: {==}
    case True{}: {==}

law and_associative:
  for a: Bool
  for +b: Bool
  for +c: Bool
  {a && (b && c) == (a && b) && c : Bool}
def and_associative(a, b, c):
  match a:
    case False{}: {==}
    case True{}: {==}

law octets_concatenate:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {B.octets_all_valid(B.concatenate(xs, ys)) == B.octets_all_valid(xs) && B.octets_all_valid(ys) : Bool}
def octets_concatenate(xs, ys):
  match xs:
    case Nil{}: {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, B.octets_all_valid(B.concatenate(t, ys)), B.octets_all_valid(t) && B.octets_all_valid(ys), octets_concatenate(t, ys)) :
        {U32.is_le(h, 255) && _ == (U32.is_le(h, 255) && B.octets_all_valid(t)) && B.octets_all_valid(ys) : Bool}
      and_associative(U32.is_le(h, 255), B.octets_all_valid(t), B.octets_all_valid(ys))


law separate_as_accept:
  for +bytes: List<&2, U32>
  {T.separate(bytes) == T.accept(B.octets_all_valid(bytes), T.header(bytes)) : Maybe<&2, T.Parts>}
def separate_as_accept(bytes):
  match bytes:
    case Nil{}: {==}
    case Con{a, Nil{}}: Equal.sym(Maybe<&2, T.Parts>, T.accept(B.octets_all_valid([a]), None{}), None{}, accept_none(B.octets_all_valid([a])))
    case Con{a, Con{b, Nil{}}}: Equal.sym(Maybe<&2, T.Parts>, T.accept(B.octets_all_valid([a,b]), None{}), None{}, accept_none(B.octets_all_valid([a,b])))
    case Con{a, Con{b, Con{c, Nil{}}}}: Equal.sym(Maybe<&2, T.Parts>, T.accept(B.octets_all_valid([a,b,c]), None{}), None{}, accept_none(B.octets_all_valid([a,b,c])))
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}: Equal.sym(Maybe<&2, T.Parts>, T.accept(B.octets_all_valid([a,b,c,d]), None{}), None{}, accept_none(B.octets_all_valid([a,b,c,d])))
    case Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}: Equal.sym(Maybe<&2, T.Parts>, T.accept(B.octets_all_valid([a,b,c,d,e]), None{}), None{}, accept_none(B.octets_all_valid([a,b,c,d,e])))
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Nil{}}}}}}}: Equal.sym(Maybe<&2, T.Parts>, T.accept(B.octets_all_valid([a,b,c,d,e,f]), None{}), None{}, accept_none(B.octets_all_valid([a,b,c,d,e,f])))
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Nil{}}}}}}}}: Equal.sym(Maybe<&2, T.Parts>, T.accept(B.octets_all_valid([a,b,c,d,e,f,g]), None{}), None{}, accept_none(B.octets_all_valid([a,b,c,d,e,f,g])))
    case Con{+a, Con{+b, Con{+c, Con{+d, Con{+e, Con{+f, Con{+g, Con{+h, +rest}}}}}}}}:
      %Equal.sym(Maybe<&2, T.Parts>, T.scan(rest, B.Number64{T.word(a,b,c,d), T.word(e,f,g,h)}),
        T.accept(B.octets_all_valid(rest), T.cut(rest, B.Number64{T.word(a,b,c,d), T.word(e,f,g,h)}, Nil{})),
        scan_without_accumulator(rest, B.Number64{T.word(a,b,c,d), T.word(e,f,g,h)})) :
        {T.accept(B.octets_all_valid([a,b,c,d,e,f,g,h]), _) == T.accept(B.octets_all_valid(Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, rest}}}}}}}}), T.cut(rest, B.Number64{T.word(a,b,c,d), T.word(e,f,g,h)}, Nil{})) : Maybe<&2, T.Parts>}
      %Equal.sym(Bool, B.octets_all_valid(B.concatenate([a,b,c,d,e,f,g,h], rest)), B.octets_all_valid([a,b,c,d,e,f,g,h]) && B.octets_all_valid(rest), octets_concatenate([a,b,c,d,e,f,g,h], rest)) :
        {T.accept(B.octets_all_valid([a,b,c,d,e,f,g,h]), T.accept(B.octets_all_valid(rest), T.cut(rest, B.Number64{T.word(a,b,c,d), T.word(e,f,g,h)}, Nil{}))) == T.accept(_, T.cut(rest, B.Number64{T.word(a,b,c,d), T.word(e,f,g,h)}, Nil{})) : Maybe<&2, T.Parts>}
      accept_nested(B.octets_all_valid([a,b,c,d,e,f,g,h]), B.octets_all_valid(rest), T.cut(rest, B.Number64{T.word(a,b,c,d), T.word(e,f,g,h)}, Nil{}))

law separate_refines_reference:
  for +bytes: List<&2, U32>
  {T.separate(bytes) == T.separate_reference(bytes) : Maybe<&2, T.Parts>}
def separate_refines_reference(bytes):
  Equal.trans(Maybe<&2, T.Parts>, T.separate(bytes), T.accept(B.octets_all_valid(bytes), T.header(bytes)),
    T.separate_reference(bytes), separate_as_accept(bytes),
    Equal.sym(Maybe<&2, T.Parts>, T.validate(B.octets_all_valid(bytes), bytes),
      T.accept(B.octets_all_valid(bytes), T.header(bytes)), validate_accept(B.octets_all_valid(bytes), bytes)))

law complete_accept:
  for ok: Bool
  for +parts: Maybe<&2, T.Parts>
  {T.complete(T.accept(ok, parts)) == T.accept(ok, T.complete(parts)) : Maybe<&2, T.Parts>}
def complete_accept(ok, parts):
  match ok:
    case False{}: {==}
    case True{}: {==}

law prepend_accept:
  for ok: Bool
  for +h: U32
  for +parts: Maybe<&2, T.Parts>
  {T.prepend(h, T.accept(ok, parts)) == T.accept(ok, T.prepend(h, parts)) : Maybe<&2, T.Parts>}
def prepend_accept(ok, h, parts):
  match ok:
    case False{}: {==}
    case True{}: {==}

law complete_prepend:
  for +h: U32
  for parts: Maybe<&2, T.Parts>
  {T.complete(T.prepend(h, parts)) == T.prepend(h, T.complete(parts)) : Maybe<&2, T.Parts>}
def complete_prepend(h, parts):
  match parts:
    case None{}: {==}
    case Some{T.Parts{first, +second}}:
      Equal.sym(Maybe<&2, T.Parts>, T.prepend(h, T.accept(B.octets_all_valid(second), Some{T.Parts{first, second}})),
        T.accept(B.octets_all_valid(second), Some{T.Parts{Con{h, first}, second}}),
        prepend_accept(B.octets_all_valid(second), h, Some{T.Parts{first, second}}))

law complete_empty:
  for ok: Bool
  {T.complete(T.accept(ok, Some{T.Parts{Nil{}, Nil{}}})) == T.accept(ok, Some{T.Parts{Nil{}, Nil{}}}) : Maybe<&2, T.Parts>}
def complete_empty(ok):
  match ok:
    case False{}: {==}
    case True{}: {==}

law prefix_step_complete:
  for zero: Bool
  for +h: U32
  for +t: List<&2, U32>
  for +count: B.Number64
  for ih: {T.complete(T.prefix_scan(t, C.decrease64(count))) == T.scan(t, C.decrease64(count)) : Maybe<&2, T.Parts>}
  {T.complete(T.prefix_step(zero, h, t, unit => T.prefix_scan(t, C.decrease64(count)))) == T.scan_step(zero, h, t, unit => T.scan(t, C.decrease64(count))) : Maybe<&2, T.Parts>}
def prefix_step_complete(zero, h, t, count, ih):
  match zero:
    case True{}: {==}
    case False{}:
      %Equal.sym(Maybe<&2, T.Parts>, T.complete(T.accept(U32.is_le(h, 255), T.prepend(h, T.prefix_scan(t, C.decrease64(count))))),
        T.accept(U32.is_le(h, 255), T.complete(T.prepend(h, T.prefix_scan(t, C.decrease64(count))))),
        complete_accept(U32.is_le(h, 255), T.prepend(h, T.prefix_scan(t, C.decrease64(count))))) :
        {_ == T.scan_step(False{}, h, t, unit => T.scan(t, C.decrease64(count))) : Maybe<&2, T.Parts>}
      %Equal.sym(Maybe<&2, T.Parts>, T.complete(T.prepend(h, T.prefix_scan(t, C.decrease64(count)))),
        T.prepend(h, T.complete(T.prefix_scan(t, C.decrease64(count)))),
        complete_prepend(h, T.prefix_scan(t, C.decrease64(count)))) :
        {T.accept(U32.is_le(h, 255), _) == T.scan_step(False{}, h, t, unit => T.scan(t, C.decrease64(count))) : Maybe<&2, T.Parts>}
      Equal.cong(Maybe<&2, T.Parts>, Maybe<&2, T.Parts>, p => T.accept(U32.is_le(h, 255), T.prepend(h, p)),
        T.complete(T.prefix_scan(t, C.decrease64(count))), T.scan(t, C.decrease64(count)), ih)

law prefix_scan_complete:
  for +bytes: List<&2, U32>
  for +count: B.Number64
  {T.complete(T.prefix_scan(bytes, count)) == T.scan(bytes, count) : Maybe<&2, T.Parts>}
def prefix_scan_complete(bytes, count):
  match bytes:
    case Nil{}: complete_empty(C.zero64(count))
    case Con{+h, +t}:
      prefix_step_complete(C.zero64(count), h, t, count, prefix_scan_complete(t, C.decrease64(count)))

law separate_prefix_complete:
  for +bytes: List<&2, U32>
  {T.complete(T.separate_prefix(bytes)) == T.separate(bytes) : Maybe<&2, T.Parts>}
def separate_prefix_complete(bytes):
  match bytes:
    case Nil{}: {==}
    case Con{a, Nil{}}: {==}
    case Con{a, Con{b, Nil{}}}: {==}
    case Con{a, Con{b, Con{c, Nil{}}}}: {==}
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}: {==}
    case Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}: {==}
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Nil{}}}}}}}: {==}
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Nil{}}}}}}}}: {==}
    case Con{+a, Con{+b, Con{+c, Con{+d, Con{+e, Con{+f, Con{+g, Con{+h, +rest}}}}}}}}:
      Equal.trans(Maybe<&2, T.Parts>,
        T.complete(T.accept(B.octets_all_valid([a,b,c,d,e,f,g,h]), T.prefix_scan(rest, B.Number64{T.word(a,b,c,d), T.word(e,f,g,h)}))),
        T.accept(B.octets_all_valid([a,b,c,d,e,f,g,h]), T.complete(T.prefix_scan(rest, B.Number64{T.word(a,b,c,d), T.word(e,f,g,h)}))),
        T.accept(B.octets_all_valid([a,b,c,d,e,f,g,h]), T.scan(rest, B.Number64{T.word(a,b,c,d), T.word(e,f,g,h)})),
        complete_accept(B.octets_all_valid([a,b,c,d,e,f,g,h]), T.prefix_scan(rest, B.Number64{T.word(a,b,c,d), T.word(e,f,g,h)})),
        Equal.cong(Maybe<&2, T.Parts>, Maybe<&2, T.Parts>, p => T.accept(B.octets_all_valid([a,b,c,d,e,f,g,h]), p),
          T.complete(T.prefix_scan(rest, B.Number64{T.word(a,b,c,d), T.word(e,f,g,h)})), T.scan(rest, B.Number64{T.word(a,b,c,d), T.word(e,f,g,h)}),
          prefix_scan_complete(rest, B.Number64{T.word(a,b,c,d), T.word(e,f,g,h)})))

law accept_idempotent:
  for ok: Bool
  for +parts: Maybe<&2, T.Parts>
  {T.accept(ok, T.accept(ok, parts)) == T.accept(ok, parts) : Maybe<&2, T.Parts>}
def accept_idempotent(ok, parts):
  match ok:
    case False{}: {==}
    case True{}: {==}

law separate_is_validated:
  for +bytes: List<&2, U32>
  {T.accept(B.octets_all_valid(bytes), T.separate(bytes)) == T.separate(bytes) : Maybe<&2, T.Parts>}
def separate_is_validated(bytes):
  %Equal.sym(Maybe<&2, T.Parts>, T.separate(bytes), T.separate_reference(bytes), separate_refines_reference(bytes)) :
    {T.accept(B.octets_all_valid(bytes), _) == _ : Maybe<&2, T.Parts>}
  %Equal.sym(Maybe<&2, T.Parts>, T.validate(B.octets_all_valid(bytes), bytes), T.accept(B.octets_all_valid(bytes), T.header(bytes)), validate_accept(B.octets_all_valid(bytes), bytes)) :
    {T.accept(B.octets_all_valid(bytes), _) == _ : Maybe<&2, T.Parts>}
  accept_idempotent(B.octets_all_valid(bytes), T.header(bytes))
