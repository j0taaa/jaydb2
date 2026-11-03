# A child root can be linked to any outer stack. Guards
# still consult the REAL stack, including pending siblings.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F

def link_stack(p: C.Stack, +outside: C.Stack) -> C.Stack:
  match p:
    case C.Root{}:
      outside
    case C.ListFrame{u, q, xs, parent}:
      C.ListFrame{u, q, xs, link_stack(parent, outside)}
    case C.Name{u, q, n, xs, parent}:
      C.Name{u, q, n, xs, link_stack(parent, outside)}
    case C.Field{u, q, n, xs, parent}:
      C.Field{u, q, n, xs, link_stack(parent, outside)}

def link(m: C.Machine, +outside: C.Stack) -> C.Machine:
  match m:
    case C.Tag{p}:
      C.Tag{link_stack(p, outside)}
    case C.TagName{p}:
      C.TagName{link_stack(p, outside)}
    case C.WordInput{f, n, a, b, p}:
      C.WordInput{f, n, a, b, link_stack(p, outside)}
    case C.Content{name, u, q, cp, s, p}:
      C.Content{name, u, q, cp, s, link_stack(p, outside)}
    case C.DecodedReady{v}:
      C.emit(outside, v)
    case C.Invalid{}:
      C.Invalid{}
    case C.Above{}:
      C.Above{}

# Only a name at root level would need a second return type.
# Reading ONE VALUE never reaches this state; record names
# always have the Name frame created by opening the record itself.
def NotRoot(p: C.Stack) -> Type:
  match p:
    case C.Root{}:
      Empty
    case _:
      Unit

def PurposeInternal(f: C.Purpose, p: C.Stack) -> Type:
  match f:
    case C.NameText{}:
      NotRoot(p)
    case _:
      Unit

def TextInternal(name: Bool, p: C.Stack) -> Type:
  match name:
    case True{}:
      NotRoot(p)
    case False{}:
      Unit

def Internal(m: C.Machine) -> Type:
  match m:
    case C.TagName{p}:
      NotRoot(p)
    case C.WordInput{f, n, a, b, p}:
      PurposeInternal(f, p)
    case C.Content{name, u, q, cp, s, p}:
      TextInternal(name, p)
    case _:
      Unit

def Continue(m: C.Machine) -> Type:
  match m:
    case C.DecodedReady{v}:
      Empty
    case _:
      Unit

def duplicate_negative_root(+p: C.Stack, h: NotRoot(p)) -> L.E<NotRoot(p), NotRoot(p)>:
  match p:
    case C.Root{}:
      L.ex_false(L.E<Empty, Empty>, h)
    case C.ListFrame{u, q, xs, parent}:
      L.Both{Unit{}, Unit{}}
    case C.Name{u, q, n, xs, parent}:
      L.Both{Unit{}, Unit{}}
    case C.Field{u, q, n, xs, parent}:
      L.Both{Unit{}, Unit{}}

def duplicate_purpose(f: C.Purpose, +p: C.Stack, h: PurposeInternal(f, p)) ->
  L.E<PurposeInternal(f, p), PurposeInternal(f, p)>:
  match f:
    case C.NameText{}:
      duplicate_negative_root(p, h)
    case C.Integer{}:
      L.Both{Unit{}, Unit{}}
    case C.TextValue{}:
      L.Both{Unit{}, Unit{}}
    case C.CountsList{}:
      L.Both{Unit{}, Unit{}}
    case C.CountsRecord{}:
      L.Both{Unit{}, Unit{}}

def duplicate_text(name: Bool, +p: C.Stack, h: TextInternal(name, p)) -> L.E<TextInternal(name, p), TextInternal(name, p)>:
  match name:
    case True{}:
      duplicate_negative_root(p, h)
    case False{}:
      L.Both{Unit{}, Unit{}}

def duplicate_internal(+m: C.Machine, h: Internal(m)) -> L.E<Internal(m), Internal(m)>:
  match m:
    case C.Tag{p}:
      L.Both{Unit{}, Unit{}}
    case C.TagName{+p}:
      duplicate_negative_root(p, h)
    case C.WordInput{+f, n, a, b, +p}:
      duplicate_purpose(f, p, h)
    case C.Content{+name, u, q, cp, s, +p}:
      duplicate_text(name, p, h)
    case C.DecodedReady{v}:
      L.Both{Unit{}, Unit{}}
    case C.Invalid{}:
      L.Both{Unit{}, Unit{}}
    case C.Above{}:
      L.Both{Unit{}, Unit{}}

law emit_commutes_combined_to_stack_external:
  for +p: C.Stack
  for +outside: C.Stack
  for +v: D.Value
  {link(C.emit(p, v), outside) == C.emit(link_stack(p, outside), v) : C.Machine}
def emit_commutes_combined_to_stack_external(p, outside, v):
  match p:
    case C.Root{}:
      {==}
    case C.ListFrame{True{}, q, xs, +parent}:
      emit_commutes_combined_to_stack_external(parent, outside, C.assemble_list(Con{v, xs}, D.VListEmpty{}))
    case C.ListFrame{False{}, q, xs, parent}:
      {==}
    case C.Field{True{}, q, n, xs, +parent}:
      emit_commutes_combined_to_stack_external(parent, outside, C.assemble_record(Con{D.Field{n, v}, xs}, D.VRecordEmpty{}))
    case C.Field{False{}, q, n, xs, parent}:
      {==}
    case C.Name{u, q, n, xs, parent}:
      {==}

def emit_internal(p: C.Stack, v: D.Value) -> Internal(C.emit(p, v)):
  match p:
    case C.Root{}:
      Unit{}
    case C.ListFrame{True{}, q, xs, parent}:
      emit_internal(parent, C.assemble_list(Con{v, xs}, D.VListEmpty{}))
    case C.ListFrame{False{}, q, xs, parent}:
      Unit{}
    case C.Field{True{}, q, n, xs, parent}:
      emit_internal(parent, C.assemble_record(Con{D.Field{n, v}, xs}, D.VRecordEmpty{}))
    case C.Field{False{}, q, n, xs, parent}:
      Unit{}
    case C.Name{u, q, n, xs, parent}:
      Unit{}

def name_checked_linked(ok: Bool, +u: Bool, +q: B.Number64,
  +n: String, +xs: List<&2, D.Field>, +p: C.Stack, +outside: C.Stack) ->
  {link(C.name_checked(ok, u, q, n, xs, p), outside) ==
    C.name_checked(ok, u, q, n, xs, link_stack(p, outside)) : C.Machine}:
  match ok:
    case False{}:
      {==}
    case True{}:
      {==}

def emit_name_linked(+p: C.Stack, +n: String, +outside: C.Stack,
  internal: NotRoot(p)) ->
  {link(C.emit_name(p, n), outside) == C.emit_name(link_stack(p, outside), n) : C.Machine}:
  match p:
    case C.Root{}:
      L.ex_false({C.Invalid{} == C.emit_name(outside, n) : C.Machine}, internal)
    case C.Name{+u, +q, +previous, +xs, +parent}:
      name_checked_linked(D.name_valid(n) && String.is_lt(previous, n), u, q, n, xs, parent, outside)
    case C.ListFrame{u, q, xs, parent}:
      {==}
    case C.Field{u, q, k, xs, parent}:
      {==}

def name_checked_internal(ok: Bool, u: Bool, q: B.Number64,
  n: String, xs: List<&2, D.Field>, p: C.Stack) -> Internal(C.name_checked(ok, u, q, n, xs, p)):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      Unit{}

def emit_name_internal(p: C.Stack, +n: String) -> Internal(C.emit_name(p, n)):
  match p:
    case C.Name{u, q, +previous, xs, parent}:
      name_checked_internal(D.name_valid(n) && String.is_lt(previous, n), u, q, n, xs, parent)
    case C.Root{}:
      Unit{}
    case C.ListFrame{u, q, xs, parent}:
      Unit{}
    case C.Field{u, q, k, xs, parent}:
      Unit{}

def emit_text_linked(name: Bool, +s: String, +p: C.Stack, +outside: C.Stack,
  internal: TextInternal(name, p)) ->
  {link(C.emit_text(name, s, p), outside) == C.emit_text(name, s, link_stack(p, outside)) : C.Machine}:
  match name:
    case False{}:
      emit_commutes_combined_to_stack_external(p, outside, D.VText{s})
    case True{}:
      emit_name_linked(p, s, outside, internal)

def emit_text_internal(name: Bool, s: String, p: C.Stack) -> Internal(C.emit_text(name, s, p)):
  match name:
    case False{}:
      emit_internal(p, D.VText{s})
    case True{}:
      emit_name_internal(p, s)

def store_character_linked(last: Bool, +name: Bool, +q: B.Number64,
  +s: String, +p: C.Stack, +outside: C.Stack, internal: TextInternal(name, p)) ->
  {link(C.store_character(last, name, q, s, p), outside) ==
    C.store_character(last, name, q, s, link_stack(p, outside)) : C.Machine}:
  match last:
    case True{}:
      emit_text_linked(name, String.reverse(s), p, outside, internal)
    case False{}:
      {==}

def store_partial_linked(last: Bool, +name: Bool, +q: B.Number64,
  +u: C.Unicode, +s: String, +p: C.Stack, +outside: C.Stack) ->
  {link(C.store_partial(last, name, q, u, s, p), outside) ==
    C.store_partial(last, name, q, u, s, link_stack(p, outside)) : C.Machine}:
  match last:
    case True{}:
      {==}
    case False{}:
      {==}

def store_scalar_linked(e: C.Scalar, +last: Bool, +name: Bool, +q: B.Number64,
  +s: String, +p: C.Stack, +outside: C.Stack, internal: TextInternal(name, p)) ->
  {link(C.store_scalar(e, last, name, q, s, p), outside) ==
    C.store_scalar(e, last, name, q, s, link_stack(p, outside)) : C.Machine}:
  match e:
    case C.UTFInvalid{}:
      {==}
    case C.Character{cp}:
      store_character_linked(last, name, q, SCon{Chr{cp}, s}, p, outside, internal)
    case C.Partial{u}:
      store_partial_linked(last, name, q, u, s, p, outside)

def store_character_internal(last: Bool, +name: Bool, q: B.Number64,
  s: String, +p: C.Stack, internal: TextInternal(name, p)) -> Internal(C.store_character(last, name, q, s, p)):
  match last:
    case True{}:
      emit_text_internal(name, String.reverse(s), p)
    case False{}:
      internal

def store_partial_internal(last: Bool, +name: Bool, q: B.Number64,
  u: C.Unicode, s: String, +p: C.Stack, internal: TextInternal(name, p)) -> Internal(C.store_partial(last, name, q, u, s, p)):
  match last:
    case True{}:
      Unit{}
    case False{}:
      internal

def store_scalar_internal(e: C.Scalar, last: Bool, +name: Bool, q: B.Number64,
  s: String, +p: C.Stack, internal: TextInternal(name, p)) -> Internal(C.store_scalar(e, last, name, q, s, p)):
  match e:
    case C.UTFInvalid{}:
      Unit{}
    case C.Character{cp}:
      store_character_internal(last, name, q, SCon{Chr{cp}, s}, p, internal)
    case C.Partial{u}:
      store_partial_internal(last, name, q, u, s, p, internal)

def open_name_linked(ok: Bool, +q: B.Number64, +p: C.Stack, +outside: C.Stack) ->
  {link(C.open_name(ok, q, p), outside) == C.open_name(ok, q, link_stack(p, outside)) : C.Machine}:
  match ok:
    case False{}:
      {==}
    case True{}:
      {==}

def open_variable_linked(empty: Bool, f: C.Purpose, +q: B.Number64, +p: C.Stack, +outside: C.Stack) ->
  {link(C.open_variable(empty, f, q, p), outside) == C.open_variable(empty, f, q, link_stack(p, outside)) : C.Machine}:
  match empty f:
    case True{} C.TextValue{}:
      emit_commutes_combined_to_stack_external(p, outside, D.VText{""})
    case True{} C.CountsList{}:
      emit_commutes_combined_to_stack_external(p, outside, D.VListEmpty{})
    case True{} C.CountsRecord{}:
      emit_commutes_combined_to_stack_external(p, outside, D.VRecordEmpty{})
    case False{} C.NameText{}:
      open_name_linked(C.less_equal64(q, B.Number64{0, 64}), q, p, outside)
    case False{} C.TextValue{}:
      {==}
    case False{} C.CountsList{}:
      {==}
    case False{} C.CountsRecord{}:
      {==}
    case True{} C.NameText{}:
      {==}
    case _ C.Integer{}:
      {==}

def open_name_internal(ok: Bool, q: B.Number64, +p: C.Stack,
  internal: NotRoot(p)) -> Internal(C.open_name(ok, q, p)):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      internal

def open_variable_internal(empty: Bool, +f: C.Purpose, +q: B.Number64, +p: C.Stack,
  internal: PurposeInternal(f, p)) -> Internal(C.open_variable(empty, f, q, p)):
  match empty f:
    case True{} C.TextValue{}:
      emit_internal(p, D.VText{""})
    case True{} C.CountsList{}:
      emit_internal(p, D.VListEmpty{})
    case True{} C.CountsRecord{}:
      emit_internal(p, D.VRecordEmpty{})
    case False{} C.TextValue{}:
      Unit{}
    case False{} C.NameText{}:
      open_name_internal(C.less_equal64(q, B.Number64{0, 64}), q, p, internal)
    case False{} C.CountsList{}:
      Unit{}
    case False{} C.CountsRecord{}:
      Unit{}
    case True{} C.NameText{}:
      Unit{}
    case _ C.Integer{}:
      Unit{}

def open_checked_linked(c: C.Check, +f: C.Purpose, +q: B.Number64, +p: C.Stack, +outside: C.Stack) ->
  {link(C.open_checked(c, f, q, p), outside) == C.open_checked(c, f, q, link_stack(p, outside)) : C.Machine}:
  match c:
    case C.Fits{}:
      open_variable_linked(C.zero64(q), f, q, p, outside)
    case C.Short{}:
      {==}
    case C.Large{}:
      {==}

def open_checked_internal(c: C.Check, +f: C.Purpose, +q: B.Number64, +p: C.Stack,
  internal: PurposeInternal(f, p)) -> Internal(C.open_checked(c, f, q, p)):
  match c:
    case C.Fits{}:
      open_variable_internal(C.zero64(q), f, q, p, internal)
    case C.Short{}:
      Unit{}
    case C.Large{}:
      Unit{}

# This is the sole difference of the local machine: the guard sees the linked stack.
# No guard is removed and no real counter is replaced.
def conclude_local(f: C.Purpose, +a: U32, +b: U32, +p: C.Stack, outside: C.Stack,
  body: B.Number64, ceiling: B.Number64) -> C.Machine:
  match f:
    case C.Integer{}:
      C.emit(p, D.VInt{a, b})
    case +other:
      +q = {B.Number64{a, b} : B.Number64}
      C.open_checked(C.check(C.sum_optional(C.minimum_field(other, q), C.minimum_stack(link_stack(p, outside))), body, ceiling), other, q, p)

def read_local(n: Nat, +f: C.Purpose, +a: U32, +b: U32, +x: U32,
  +p: C.Stack, outside: C.Stack, body: B.Number64, ceiling: B.Number64) -> C.Machine:
  match n:
    case 0n:
      conclude_local(f, (a * 256 + U32.shrn(b, 24n) : U32), (b * 256 + x : U32), p, outside, body, ceiling)
    case 1n+k:
      C.WordInput{f, k, (a * 256 + U32.shrn(b, 24n) : U32), (b * 256 + x : U32), p}

def step_local(m: C.Machine, +outside: C.Stack, b: U32, body: B.Number64, ceiling: B.Number64) -> C.Machine:
  match m:
    case C.WordInput{f, n, a, c, p}:
      read_local(n, f, a, c, b, p, outside, body, ceiling)
    case +other:
      C.step(other, b, body, ceiling)

def conclude_local_linked(+f: C.Purpose, +a: U32, +b: U32, +p: C.Stack, +outside: C.Stack,
  +body: B.Number64, +ceiling: B.Number64) ->
  {link(conclude_local(f, a, b, p, outside, body, ceiling), outside) == C.conclude_word(f, a, b, link_stack(p, outside), body, ceiling) : C.Machine}:
  match f:
    case C.Integer{}:
      emit_commutes_combined_to_stack_external(p, outside, D.VInt{a, b})
    case C.TextValue{}:
      +q = {B.Number64{a, b} : B.Number64}
      open_checked_linked(C.check(C.sum_optional(C.minimum_field(C.TextValue{}, q), C.minimum_stack(link_stack(p, outside))), body, ceiling), C.TextValue{}, q, p, outside)
    case C.NameText{}:
      +q = {B.Number64{a, b} : B.Number64}
      open_checked_linked(C.check(C.sum_optional(C.minimum_field(C.NameText{}, q), C.minimum_stack(link_stack(p, outside))), body, ceiling), C.NameText{}, q, p, outside)
    case C.CountsList{}:
      +q = {B.Number64{a, b} : B.Number64}
      open_checked_linked(C.check(C.sum_optional(C.minimum_field(C.CountsList{}, q), C.minimum_stack(link_stack(p, outside))), body, ceiling), C.CountsList{}, q, p, outside)
    case C.CountsRecord{}:
      +q = {B.Number64{a, b} : B.Number64}
      open_checked_linked(C.check(C.sum_optional(C.minimum_field(C.CountsRecord{}, q), C.minimum_stack(link_stack(p, outside))), body, ceiling), C.CountsRecord{}, q, p, outside)

def conclude_local_internal(+f: C.Purpose, +a: U32, +b: U32, +p: C.Stack, outside: C.Stack,
  body: B.Number64, ceiling: B.Number64, internal: PurposeInternal(f, p)) -> Internal(conclude_local(f, a, b, p, outside, body, ceiling)):
  match f:
    case C.Integer{}:
      emit_internal(p, D.VInt{a, b})
    case C.TextValue{}:
      +q = {B.Number64{a, b} : B.Number64}
      open_checked_internal(C.check(C.sum_optional(C.minimum_field(C.TextValue{}, q), C.minimum_stack(link_stack(p, outside))), body, ceiling), C.TextValue{}, q, p, internal)
    case C.NameText{}:
      +q = {B.Number64{a, b} : B.Number64}
      open_checked_internal(C.check(C.sum_optional(C.minimum_field(C.NameText{}, q), C.minimum_stack(link_stack(p, outside))), body, ceiling), C.NameText{}, q, p, internal)
    case C.CountsList{}:
      +q = {B.Number64{a, b} : B.Number64}
      open_checked_internal(C.check(C.sum_optional(C.minimum_field(C.CountsList{}, q), C.minimum_stack(link_stack(p, outside))), body, ceiling), C.CountsList{}, q, p, internal)
    case C.CountsRecord{}:
      +q = {B.Number64{a, b} : B.Number64}
      open_checked_internal(C.check(C.sum_optional(C.minimum_field(C.CountsRecord{}, q), C.minimum_stack(link_stack(p, outside))), body, ceiling), C.CountsRecord{}, q, p, internal)

def read_local_linked(n: Nat, +f: C.Purpose, +a: U32, +b: U32, +x: U32,
  +p: C.Stack, +outside: C.Stack, +body: B.Number64, +ceiling: B.Number64) ->
  {link(read_local(n, f, a, b, x, p, outside, body, ceiling), outside) == C.read_word(n, f, a, b, x, link_stack(p, outside), body, ceiling) : C.Machine}:
  match n:
    case 0n:
      conclude_local_linked(f, (a * 256 + U32.shrn(b, 24n) : U32), (b * 256 + x : U32), p, outside, body, ceiling)
    case 1n+k:
      {==}

def read_local_internal(n: Nat, +f: C.Purpose, a: U32, +b: U32, x: U32,
  +p: C.Stack, outside: C.Stack, body: B.Number64, ceiling: B.Number64,
  internal: PurposeInternal(f, p)) -> Internal(read_local(n, f, a, b, x, p, outside, body, ceiling)):
  match n:
    case 0n:
      conclude_local_internal(f, (a * 256 + U32.shrn(b, 24n) : U32), (b * 256 + x : U32), p, outside, body, ceiling, internal)
    case 1n+k:
      internal

def read_tag_linked(n: Nat, +p: C.Stack, +outside: C.Stack) ->
  {link(C.read_tag(n, p), outside) == C.read_tag(n, link_stack(p, outside)) : C.Machine}:
  match n:
    case 0n:
      emit_commutes_combined_to_stack_external(p, outside, D.VAbsent{})
    case 1n:
      emit_commutes_combined_to_stack_external(p, outside, D.VBool{False{}})
    case 2n:
      emit_commutes_combined_to_stack_external(p, outside, D.VBool{True{}})
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n+k:
      {==}

def read_tag_internal(n: Nat, p: C.Stack) -> Internal(C.read_tag(n, p)):
  match n:
    case 0n:
      emit_internal(p, D.VAbsent{})
    case 1n:
      emit_internal(p, D.VBool{False{}})
    case 2n:
      emit_internal(p, D.VBool{True{}})
    case 3n:
      Unit{}
    case 4n:
      Unit{}
    case 5n:
      Unit{}
    case 6n:
      Unit{}
    case 7n+k:
      Unit{}

def read_tag_name_linked(ok: Bool, +p: C.Stack, +outside: C.Stack) ->
  {link(C.read_tag_name(ok, p), outside) == C.read_tag_name(ok, link_stack(p, outside)) : C.Machine}:
  match ok:
    case False{}:
      {==}
    case True{}:
      {==}

def read_tag_name_internal(ok: Bool, +p: C.Stack, internal: NotRoot(p)) -> Internal(C.read_tag_name(ok, p)):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      internal

law step_local_linked_and_o_step_real:
  for +m: C.Machine
  for +outside: C.Stack
  for +b: U32
  for +body: B.Number64
  for +ceiling: B.Number64
  for internal: Internal(m)
  for continues: Continue(m)
  {link(step_local(m, outside, b, body, ceiling), outside) == C.step(link(m, outside), b, body, ceiling) : C.Machine}
def step_local_linked_and_o_step_real(m, outside, b, body, ceiling, internal, continues):
  match m:
    case C.Tag{+p}:
      read_tag_linked(U32.to_nat(b), p, outside)
    case C.TagName{+p}:
      read_tag_name_linked(U32.is_eq(b, 4), p, outside)
    case C.WordInput{+f, +n, +a, +c, +p}:
      read_local_linked(n, f, a, c, b, p, outside, body, ceiling)
    case C.Content{+name, +last, +q, +u, +s, +p}:
      store_scalar_linked(C.step_utf8(u, b), last, name, q, s, p, outside, internal)
    case C.DecodedReady{+v}:
      L.ex_false({C.Invalid{} == C.step(C.emit(outside, v), b, body, ceiling) : C.Machine}, continues)
    case C.Invalid{}:
      {==}
    case C.Above{}:
      {==}

law step_local_preserves_interior:
  for +m: C.Machine
  for outside: C.Stack
  for +b: U32
  for body: B.Number64
  for ceiling: B.Number64
  for internal: Internal(m)
  Internal(step_local(m, outside, b, body, ceiling))
def step_local_preserves_interior(m, outside, b, body, ceiling, internal):
  match m:
    case C.Tag{p}:
      read_tag_internal(U32.to_nat(b), p)
    case C.TagName{+p}:
      read_tag_name_internal(U32.is_eq(b, 4), p, internal)
    case C.WordInput{+f, n, a, c, +p}:
      read_local_internal(n, f, a, c, b, p, outside, body, ceiling, internal)
    case C.Content{+name, last, q, u, s, +p}:
      store_scalar_internal(C.step_utf8(u, b), last, name, q, s, p, internal)
    case C.DecodedReady{v}:
      Unit{}
    case C.Invalid{}:
      Unit{}
    case C.Above{}:
      Unit{}
