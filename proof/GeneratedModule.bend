# Parse both context and argument declarations from actual generated source;
# the parser does not receive the expected context as an input. Official
# frontend/compiler agreement remains separate from this restricted grammar.
import Base
import ../contract/Data.bend as D
import ../contract/Bytes.bend as B
import ../contract/Protocol.bend as P
import ../src/Generate.bend as G
import ../src/Reification.bend as R
import ./GeneratedInstance.bend as I
import ./GeneratedContext.bend as C
import ./GeneratedArgumentCall.bend as A
import ./GeneratedLiterals.bend as L
import ./DecimalShow.bend as S

type ModuleRead is Data:
  ModuleInvalid{}
  ModuleInstance{context: D.Context, arguments: D.Value, rest: String}

def with_arguments(ctx: D.Context, parsed: A.ArgumentRead) -> ModuleRead:
  match parsed:
    case A.ArgumentInvalid{}: ModuleInvalid{}
    case A.ArgumentRead{value, rest}: ModuleInstance{ctx, value, rest}

def after_arguments_prefix(ctx: D.Context, fuel: Nat, remaining: Maybe<&2, String>) -> ModuleRead:
  match remaining:
    case None{}: ModuleInvalid{}
    case Some{raw}: with_arguments(ctx, A.parse_argument(fuel, raw))

def with_context(fuel: Nat, parsed: C.ContextRead) -> ModuleRead:
  match parsed:
    case C.Invalid{}: ModuleInvalid{}
    case C.Context{ctx, rest}: after_arguments_prefix(ctx, fuel, C.strip(I.before_arguments(), rest))

def after_header(id_fuel: Nat, kind_fuel: Nat, arg_fuel: Nat, remaining: Maybe<&2, String>) -> ModuleRead:
  match remaining:
    case None{}: ModuleInvalid{}
    case Some{raw}: with_context(arg_fuel, C.parse(id_fuel, kind_fuel, raw))

def parse_instance(id_fuel: Nat, kind_fuel: Nat, arg_fuel: Nat, source: String) -> ModuleRead:
  after_header(id_fuel, kind_fuel, arg_fuel, C.strip(I.header(), source))

law actual_instance_layout_has_context_and_argument_declarations:
  for +ctx: D.Context
  for +bytes: List<&2, U32>
  for +hi: U32
  for +lo: U32
  {G.instance_content(ctx, bytes, hi, lo) == I.header() ++
    (G.context(ctx) ++ (I.before_arguments() ++ A.argument_call(R.text(bytes), hi, lo, "\n"))) : String}
def actual_instance_layout_has_context_and_argument_declarations(ctx, bytes, hi, lo):
  Equal.trans(String, G.instance_content(ctx, bytes, hi, lo),
    I.prefix(ctx) ++ A.argument_call(R.text(bytes), hi, lo, "\n"),
    I.header() ++ (G.context(ctx) ++ (I.before_arguments() ++ A.argument_call(R.text(bytes), hi, lo, "\n"))),
    I.actual_generator_exposes_exact_numeric_call(ctx, bytes, hi, lo),
    Equal.trans(String, I.prefix(ctx) ++ A.argument_call(R.text(bytes), hi, lo, "\n"),
      I.header() ++ ((G.context(ctx) ++ I.before_arguments()) ++ A.argument_call(R.text(bytes), hi, lo, "\n")),
      I.header() ++ (G.context(ctx) ++ (I.before_arguments() ++ A.argument_call(R.text(bytes), hi, lo, "\n"))),
      S.string_append_associative(I.header(), G.context(ctx) ++ I.before_arguments(), A.argument_call(R.text(bytes), hi, lo, "\n")),
      Equal.cong(String, String, rest => I.header() ++ rest,
        (G.context(ctx) ++ I.before_arguments()) ++ A.argument_call(R.text(bytes), hi, lo, "\n"),
        G.context(ctx) ++ (I.before_arguments() ++ A.argument_call(R.text(bytes), hi, lo, "\n")),
        S.string_append_associative(G.context(ctx), I.before_arguments(), A.argument_call(R.text(bytes), hi, lo, "\n")))))

law actual_instance_module_recovers_context_and_arguments_together:
  for +id: String
  for +kind: String
  for +value: D.Value
  for +bytes: List<&2, U32>
  for +hi: U32
  for +lo: U32
  for encoded: P.Encoding(value, bytes)
  for measured: {B.nat64(B.length(bytes)) == Some{B.Number64{hi, lo}} : Maybe<&2, B.Number64>}
  {parse_instance(Nat.add(String.length(id), 1n), Nat.add(String.length(kind), 1n), Nat.add(String.length(R.text(bytes)), 1n),
    G.instance_content(D.Context{id, kind}, bytes, hi, lo)) == ModuleInstance{D.Context{id, kind}, value, "\n"} : ModuleRead}
def actual_instance_module_recovers_context_and_arguments_together(id, kind, value, bytes, hi, lo, encoded, measured):
  %Equal.sym(String, G.instance_content(D.Context{id, kind}, bytes, hi, lo),
    I.header() ++ (G.context(D.Context{id, kind}) ++ (I.before_arguments() ++ A.argument_call(R.text(bytes), hi, lo, "\n"))),
    actual_instance_layout_has_context_and_argument_declarations(D.Context{id, kind}, bytes, hi, lo)) :
    {parse_instance(Nat.add(String.length(id), 1n), Nat.add(String.length(kind), 1n), Nat.add(String.length(R.text(bytes)), 1n), _) == ModuleInstance{D.Context{id, kind}, value, "\n"} : ModuleRead}
  %Equal.sym(Maybe<&2, String>, C.strip(I.header(), I.header() ++ (G.context(D.Context{id, kind}) ++ (I.before_arguments() ++ A.argument_call(R.text(bytes), hi, lo, "\n")))),
    Some{G.context(D.Context{id, kind}) ++ (I.before_arguments() ++ A.argument_call(R.text(bytes), hi, lo, "\n"))},
    C.stripping_an_exact_prefix_preserves_the_entire_suffix(I.header(), G.context(D.Context{id, kind}) ++ (I.before_arguments() ++ A.argument_call(R.text(bytes), hi, lo, "\n")))) :
    {after_header(Nat.add(String.length(id), 1n), Nat.add(String.length(kind), 1n), Nat.add(String.length(R.text(bytes)), 1n), _) == ModuleInstance{D.Context{id, kind}, value, "\n"} : ModuleRead}
  %Equal.sym(C.ContextRead, C.parse(Nat.add(String.length(id), 1n), Nat.add(String.length(kind), 1n),
    G.context(D.Context{id, kind}) ++ (I.before_arguments() ++ A.argument_call(R.text(bytes), hi, lo, "\n"))),
    C.Context{D.Context{id, kind}, I.before_arguments() ++ A.argument_call(R.text(bytes), hi, lo, "\n")},
    C.actual_context_reification_preserves_id_kind_and_source_suffix(id, kind, I.before_arguments() ++ A.argument_call(R.text(bytes), hi, lo, "\n"), 0n, 0n)) :
    {with_context(Nat.add(String.length(R.text(bytes)), 1n), _) == ModuleInstance{D.Context{id, kind}, value, "\n"} : ModuleRead}
  %Equal.sym(Maybe<&2, String>, C.strip(I.before_arguments(), I.before_arguments() ++ A.argument_call(R.text(bytes), hi, lo, "\n")),
    Some{A.argument_call(R.text(bytes), hi, lo, "\n")},
    C.stripping_an_exact_prefix_preserves_the_entire_suffix(I.before_arguments(), A.argument_call(R.text(bytes), hi, lo, "\n"))) :
    {after_arguments_prefix(D.Context{id, kind}, Nat.add(String.length(R.text(bytes)), 1n), _) == ModuleInstance{D.Context{id, kind}, value, "\n"} : ModuleRead}
  Equal.cong(A.ArgumentRead, ModuleRead, parsed => with_arguments(D.Context{id, kind}, parsed),
    A.parse_argument(Nat.add(String.length(R.text(bytes)), 1n), A.argument_call(R.text(bytes), hi, lo, "\n")), A.ArgumentRead{value, "\n"},
    A.actual_argument_call_recovers_value(value, bytes, hi, lo, "\n", 0n, encoded, measured))

# Complete exact literal binding for Generate.links, including the unchanged
# certificate and termination declarations following the client code literal.
def links_header() -> String:
  "import Base\n" ++ "import ./Data.bend as D\n" ++ "import ./Semantics.bend as S\n" ++
  "import ./Requirements.bend as R\n" ++ "import ./RequestFacts.bend as F\n" ++
  "import ./Instance.bend as I\n" ++ "import ./Client.bend as Client\n\n" ++
  "def code() -> String:\n  "

def links_declarations() -> String:
  "\n\nlaw certificate:\n  R.Certifies(I.config(), code(), Client.program(), I.context(), I.arguments())\n\n" ++
  "law terminates:\n  F.ProgramTerminates(I.config(), Client.program())\n"

def links_literal(fuel: Nat, remaining: Maybe<&2, String>) -> L.Parsed:
  match remaining:
    case None{}: L.Invalid{}
    case Some{raw}: L.parse(fuel, raw)

def parse_links(fuel: Nat, source: String) -> L.Parsed:
  links_literal(fuel, C.strip(links_header(), source))

law actual_links_layout_binds_literal_and_both_declarations:
  for +code: String
  {G.links(code) == links_header() ++ (G.literal(code) ++ links_declarations()) : String}
def actual_links_layout_binds_literal_and_both_declarations(code):
  {==}

law actual_links_recovers_exact_client_code_and_complete_judgment_suffix:
  for +code: String
  {parse_links(Nat.add(String.length(code), 1n), G.links(code)) == L.Literal{code, links_declarations()} : L.Parsed}
def actual_links_recovers_exact_client_code_and_complete_judgment_suffix(code):
  %Equal.sym(String, G.links(code), links_header() ++ (G.literal(code) ++ links_declarations()),
    actual_links_layout_binds_literal_and_both_declarations(code)) :
    {parse_links(Nat.add(String.length(code), 1n), _) == L.Literal{code, links_declarations()} : L.Parsed}
  %Equal.sym(Maybe<&2, String>, C.strip(links_header(), links_header() ++ (G.literal(code) ++ links_declarations())),
    Some{G.literal(code) ++ links_declarations()},
    C.stripping_an_exact_prefix_preserves_the_entire_suffix(links_header(), G.literal(code) ++ links_declarations())) :
    {links_literal(Nat.add(String.length(code), 1n), _) == L.Literal{code, links_declarations()} : L.Parsed}
  L.actual_generated_literal_roundtrip_with_arbitrary_source_suffix(code, links_declarations(), 0n)
