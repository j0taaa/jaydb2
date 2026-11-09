# General reification of the actual Generate.context source fragment.
# This independent restricted grammar consumes D.Context{literal,literal} and
# retains arbitrary following source. Official frontend/UTF16 execution remains
# a separate implementation bridge; no source-parsing success is assumed.
import Base
import ../contract/Data.bend as D
import ../src/Generate.bend as G
import ./GeneratedLiterals.bend as L
import ./Orders.bend as O

type ContextRead is Data:
  Invalid{}
  Context{value: D.Context, rest: String}

def select(ok: Bool, remaining: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case False{}: None{}
    case True{}: remaining

def strip(prefix: String, raw: String) -> Maybe<&2, String>:
  match prefix raw:
    case SNil{} rest: Some{rest}
    case SCon{head, tail} SCon{actual, rest}:
      select(Char.is_eq(head, actual), strip(tail, rest))
    case SCon{head, tail} SNil{}: None{}

def finish(value: D.Context, remaining: Maybe<&2, String>) -> ContextRead:
  match remaining:
    case None{}: Invalid{}
    case Some{rest}: Context{value, rest}

def after_kind(id: String, parsed: L.Parsed) -> ContextRead:
  match parsed:
    case L.Invalid{}: Invalid{}
    case L.Literal{kind, rest}: finish(D.Context{id, kind}, strip("}", rest))

def after_comma(id: String, fuel: Nat, remaining: Maybe<&2, String>) -> ContextRead:
  match remaining:
    case None{}: Invalid{}
    case Some{raw}: after_kind(id, L.parse(fuel, raw))

def after_id(fuel_kind: Nat, parsed: L.Parsed) -> ContextRead:
  match parsed:
    case L.Invalid{}: Invalid{}
    case L.Literal{id, rest}: after_comma(id, fuel_kind, strip(",", rest))

def after_open(fuel_id: Nat, fuel_kind: Nat, remaining: Maybe<&2, String>) -> ContextRead:
  match remaining:
    case None{}: Invalid{}
    case Some{raw}: after_id(fuel_kind, L.parse(fuel_id, raw))

def parse(fuel_id: Nat, fuel_kind: Nat, raw: String) -> ContextRead:
  after_open(fuel_id, fuel_kind, strip("D.Context{", raw))

law stripping_an_exact_prefix_preserves_the_entire_suffix:
  for prefix: String
  for +rest: String
  {strip(prefix, prefix ++ rest) == Some{rest} : Maybe<&2, String>}
def stripping_an_exact_prefix_preserves_the_entire_suffix(prefix, rest):
  match prefix:
    case SNil{}: {==}
    case SCon{Chr{n}, tail}:
      %Equal.sym(Bool, U32.is_eq(n, n), True{},
        Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), U32.cmp(n, n), EQ{}, O.u32_refl(n))) :
        {select(_, strip(tail, tail ++ rest)) == Some{rest} : Maybe<&2, String>}
      stripping_an_exact_prefix_preserves_the_entire_suffix(tail, rest)

def generated_kind_decodes(+id: String, +kind: String, +rest: String, +extra: Nat) ->
  {after_kind(id, L.parse(Nat.add(String.length(kind), 1n+extra),
    (G.literal(kind) ++ "}") ++ rest)) == Context{D.Context{id, kind}, rest} : ContextRead}:
  %Equal.sym(String, (G.literal(kind) ++ "}") ++ rest, G.literal(kind) ++ ("}" ++ rest),
    L.append_associative(G.literal(kind), "}", rest)) :
    {after_kind(id, L.parse(Nat.add(String.length(kind), 1n+extra), _)) == Context{D.Context{id, kind}, rest} : ContextRead}
  %Equal.sym(L.Parsed, L.parse(Nat.add(String.length(kind), 1n+extra), G.literal(kind) ++ ("}" ++ rest)),
    L.Literal{kind, "}" ++ rest}, L.actual_generated_literal_roundtrip_with_arbitrary_source_suffix(kind, "}" ++ rest, extra)) :
    {after_kind(id, _) == Context{D.Context{id, kind}, rest} : ContextRead}
  {==}

def generated_fields_decode(+id: String, +kind: String, +rest: String, +extra_id: Nat, +extra_kind: Nat) ->
  {after_id(Nat.add(String.length(kind), 1n+extra_kind),
    L.parse(Nat.add(String.length(id), 1n+extra_id),
      (G.literal(id) ++ ("," ++ (G.literal(kind) ++ "}"))) ++ rest)) ==
    Context{D.Context{id, kind}, rest} : ContextRead}:
  %Equal.sym(String,
    (G.literal(id) ++ ("," ++ (G.literal(kind) ++ "}"))) ++ rest,
    G.literal(id) ++ ("," ++ ((G.literal(kind) ++ "}") ++ rest)),
    L.append_associative(G.literal(id), "," ++ (G.literal(kind) ++ "}"), rest)) :
    {after_id(Nat.add(String.length(kind), 1n+extra_kind),
      L.parse(Nat.add(String.length(id), 1n+extra_id), _)) == Context{D.Context{id, kind}, rest} : ContextRead}
  %Equal.sym(L.Parsed,
    L.parse(Nat.add(String.length(id), 1n+extra_id), G.literal(id) ++ ("," ++ ((G.literal(kind) ++ "}") ++ rest))),
    L.Literal{id, "," ++ ((G.literal(kind) ++ "}") ++ rest)},
    L.actual_generated_literal_roundtrip_with_arbitrary_source_suffix(id, "," ++ ((G.literal(kind) ++ "}") ++ rest), extra_id)) :
    {after_id(Nat.add(String.length(kind), 1n+extra_kind), _) == Context{D.Context{id, kind}, rest} : ContextRead}
  generated_kind_decodes(id, kind, rest, extra_kind)

# Every Context has these two fields; neither identifier nor kind is restricted
# to a finite list, nonempty spelling, or a convenient character subset.
law actual_context_reification_preserves_id_kind_and_source_suffix:
  for +id: String
  for +kind: String
  for +rest: String
  for +extra_id: Nat
  for +extra_kind: Nat
  {parse(Nat.add(String.length(id), 1n+extra_id), Nat.add(String.length(kind), 1n+extra_kind),
    G.context(D.Context{id, kind}) ++ rest) == Context{D.Context{id, kind}, rest} : ContextRead}
def actual_context_reification_preserves_id_kind_and_source_suffix(id, kind, rest, extra_id, extra_kind):
  generated_fields_decode(id, kind, rest, extra_id, extra_kind)

def decoded_value(result: ContextRead) -> D.Context:
  match result:
    case Invalid{}: D.Context{"", ""}
    case Context{value, rest}: value

def in_common_fuel(+id: String, +kind: String, +other_id: String, +other_kind: String) ->
  {parse(Nat.add(String.length(other_id), 1n+String.length(id)),
    Nat.add(String.length(other_kind), 1n+String.length(kind)), G.context(D.Context{id, kind}) ++ "") ==
    Context{D.Context{id, kind}, ""} : ContextRead}:
  %Equal.sym(Nat, Nat.add(String.length(other_id), 1n+String.length(id)),
    Nat.add(String.length(id), 1n+String.length(other_id)), L.common_fuel(String.length(other_id), String.length(id))) :
    {parse(_, Nat.add(String.length(other_kind), 1n+String.length(kind)), G.context(D.Context{id, kind}) ++ "") ==
      Context{D.Context{id, kind}, ""} : ContextRead}
  %Equal.sym(Nat, Nat.add(String.length(other_kind), 1n+String.length(kind)),
    Nat.add(String.length(kind), 1n+String.length(other_kind)), L.common_fuel(String.length(other_kind), String.length(kind))) :
    {parse(Nat.add(String.length(id), 1n+String.length(other_id)), _, G.context(D.Context{id, kind}) ++ "") ==
      Context{D.Context{id, kind}, ""} : ContextRead}
  actual_context_reification_preserves_id_kind_and_source_suffix(id, kind, "", String.length(other_id), String.length(other_kind))

law generated_context_cannot_substitute_a_different_identity:
  for +first: D.Context
  for +second: D.Context
  for same: {G.context(first) == G.context(second) : String}
  {first == second : D.Context}
def generated_context_cannot_substitute_a_different_identity(first, second, same):
  match first second:
    case D.Context{+id, +kind} D.Context{+other_id, +other_kind}:
      Equal.cong(ContextRead, D.Context, decoded_value,
        Context{D.Context{id, kind}, ""}, Context{D.Context{other_id, other_kind}, ""},
        Equal.trans(ContextRead, Context{D.Context{id, kind}, ""},
          parse(Nat.add(String.length(id), 1n+String.length(other_id)),
            Nat.add(String.length(kind), 1n+String.length(other_kind)), G.context(D.Context{id, kind}) ++ ""),
          Context{D.Context{other_id, other_kind}, ""},
          Equal.sym(ContextRead,
            parse(Nat.add(String.length(id), 1n+String.length(other_id)),
              Nat.add(String.length(kind), 1n+String.length(other_kind)), G.context(D.Context{id, kind}) ++ ""),
            Context{D.Context{id, kind}, ""},
            actual_context_reification_preserves_id_kind_and_source_suffix(id, kind, "", String.length(other_id), String.length(other_kind))),
          Equal.trans(ContextRead,
            parse(Nat.add(String.length(id), 1n+String.length(other_id)),
              Nat.add(String.length(kind), 1n+String.length(other_kind)), G.context(D.Context{id, kind}) ++ ""),
            parse(Nat.add(String.length(id), 1n+String.length(other_id)),
              Nat.add(String.length(kind), 1n+String.length(other_kind)), G.context(D.Context{other_id, other_kind}) ++ ""),
            Context{D.Context{other_id, other_kind}, ""},
            Equal.cong(String, ContextRead,
              raw => parse(Nat.add(String.length(id), 1n+String.length(other_id)),
                Nat.add(String.length(kind), 1n+String.length(other_kind)), raw ++ ""),
              G.context(D.Context{id, kind}), G.context(D.Context{other_id, other_kind}), same),
            in_common_fuel(other_id, other_kind, id, kind))))
