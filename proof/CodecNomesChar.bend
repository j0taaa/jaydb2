# Os caracteres aceitos nos nomes do contrato pertencem ao ASCII.
# Usa os intervalos reais de Base, sem enumerar valores de U32.
import Base
import ../contrato/Dados.bend as D
import ./Fundamentos.bend as F
import ./Ordens.bend as O
import ./CodecUnicode.bend as U

# Eliminacao construtiva da disjuncao booleana.
def ou_booleano_eliminar(a: Bool, -b: Bool, -A: Type,
  aceito: {a || b == True{} : Bool},
  esquerda: {a == True{} : Bool} -> A,
  direita: {b == True{} : Bool} -> A) -> A:
  match a:
    case False{}:
      direita(aceito)
    case True{}:
      esquerda({==})

law maiuscula_e_ascii:
  for +cp: U32
  for aceito: {Char.is_upper(Chr{cp}) == True{} : Bool}
  {U32.is_lt(cp, 128) == True{} : Bool}
def maiuscula_e_ascii(cp, aceito):
  le = F.e_booleano_direita(U32.is_ge(cp, 65), U32.is_le(cp, 90), aceito)
  lt = Equal.trans(Bool, U32.is_lt(cp, 91), U32.is_le(cp, 90), True{},
    Equal.sym(Bool, U32.is_le(cp, 90), U32.is_lt(cp, 91),
      U.limite_u32_sucessor(cp, 90, {==})), le)
  U.u32_lt_transitivo(cp, 91, 128, lt, {==})

law minuscula_e_ascii:
  for +cp: U32
  for aceito: {Char.is_lower(Chr{cp}) == True{} : Bool}
  {U32.is_lt(cp, 128) == True{} : Bool}
def minuscula_e_ascii(cp, aceito):
  le = F.e_booleano_direita(U32.is_ge(cp, 97), U32.is_le(cp, 122), aceito)
  lt = Equal.trans(Bool, U32.is_lt(cp, 123), U32.is_le(cp, 122), True{},
    Equal.sym(Bool, U32.is_le(cp, 122), U32.is_lt(cp, 123),
      U.limite_u32_sucessor(cp, 122, {==})), le)
  U.u32_lt_transitivo(cp, 123, 128, lt, {==})

law alpha_e_ascii:
  for +cp: U32
  for aceito: {Char.is_alpha(Chr{cp}) == True{} : Bool}
  {U32.is_lt(cp, 128) == True{} : Bool}
def alpha_e_ascii(cp, aceito):
  ou_booleano_eliminar(Char.is_upper(Chr{cp}), Char.is_lower(Chr{cp}),
    {U32.is_lt(cp, 128) == True{} : Bool}, aceito,
    maiuscula => maiuscula_e_ascii(cp, maiuscula),
    minuscula => minuscula_e_ascii(cp, minuscula))

law digito_e_ascii:
  for +cp: U32
  for aceito: {Char.is_digit(Chr{cp}) == True{} : Bool}
  {U32.is_lt(cp, 128) == True{} : Bool}
def digito_e_ascii(cp, aceito):
  le = F.e_booleano_direita(U32.is_ge(cp, 48), U32.is_le(cp, 57), aceito)
  lt = Equal.trans(Bool, U32.is_lt(cp, 58), U32.is_le(cp, 57), True{},
    Equal.sym(Bool, U32.is_le(cp, 57), U32.is_lt(cp, 58),
      U.limite_u32_sucessor(cp, 57, {==})), le)
  U.u32_lt_transitivo(cp, 58, 128, lt, {==})

law sublinhado_e_ascii:
  for +cp: U32
  for aceito: {Char.is_eq(Chr{cp}, '_') == True{} : Bool}
  {U32.is_lt(cp, 128) == True{} : Bool}
def sublinhado_e_ascii(cp, aceito):
  %Equal.sym(U32, cp, 95,
    O.u32_igual(cp, 95, O.cmp_eq(U32.cmp(cp, 95), aceito))) :
    {U32.is_lt(_, 128) == True{} : Bool}
  {==}

law inicio_nome_e_ascii:
  for +cp: U32
  for aceito: {D.inicio_nome(Chr{cp}) == True{} : Bool}
  {U32.is_lt(cp, 128) == True{} : Bool}
def inicio_nome_e_ascii(cp, aceito):
  ou_booleano_eliminar(Char.is_alpha(Chr{cp}), Char.is_eq(Chr{cp}, '_'),
    {U32.is_lt(cp, 128) == True{} : Bool}, aceito,
    alpha => alpha_e_ascii(cp, alpha),
    sublinhado => sublinhado_e_ascii(cp, sublinhado))

law resto_caractere_e_ascii:
  for +cp: U32
  for aceito: {D.inicio_nome(Chr{cp}) || Char.is_digit(Chr{cp}) == True{} : Bool}
  {U32.is_lt(cp, 128) == True{} : Bool}
def resto_caractere_e_ascii(cp, aceito):
  ou_booleano_eliminar(D.inicio_nome(Chr{cp}), Char.is_digit(Chr{cp}),
    {U32.is_lt(cp, 128) == True{} : Bool}, aceito,
    inicio => inicio_nome_e_ascii(cp, inicio),
    digito => digito_e_ascii(cp, digito))
