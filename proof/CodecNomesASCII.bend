# Nomes do contrato sao ASCII: a medida UTF-8 e a quantidade de caracteres.
# Os intervalos reais de Char sao demonstrados em CodecNomesChar.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ./Fundamentos.bend as F
import ./CodecUnicode.bend as U
import ./CodecNomesChar.bend as H

def texto_ascii(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{cp}, t}:
      U32.is_lt(cp, 128) && texto_ascii(t)

law resto_nome_e_ascii:
  for +s: String
  for +valido: {D.resto_nome(s) == True{} : Bool}
  {texto_ascii(s) == True{} : Bool}
def resto_nome_e_ascii(s, valido):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+cp}, +t}:
      F.e_booleano_intro(U32.is_lt(cp, 128), texto_ascii(t),
        H.resto_caractere_e_ascii(cp,
          F.e_booleano_esquerda(D.inicio_nome(Chr{cp}) || Char.is_digit(Chr{cp}), D.resto_nome(t), valido)),
        resto_nome_e_ascii(t,
          F.e_booleano_direita(D.inicio_nome(Chr{cp}) || Char.is_digit(Chr{cp}), D.resto_nome(t), valido)))

law nome_valido_e_ascii:
  for +s: String
  for valido: {D.nome_valido(s) == True{} : Bool}
  {texto_ascii(s) == True{} : Bool}
def nome_valido_e_ascii(s, valido):
  match s:
    case SNil{}:
      F.absurdo_booleano({True{} == True{} : Bool}, valido)
    case SCon{Chr{+cp}, +t}:
      +caracteres = F.e_booleano_esquerda(D.inicio_nome(Chr{cp}) && D.resto_nome(t),
        Nat.is_le(String.length(SCon{Chr{cp}, t}), 64n), valido)
      F.e_booleano_intro(U32.is_lt(cp, 128), texto_ascii(t),
        H.inicio_nome_e_ascii(cp, F.e_booleano_esquerda(D.inicio_nome(Chr{cp}), D.resto_nome(t), caracteres)),
        resto_nome_e_ascii(t, F.e_booleano_direita(D.inicio_nome(Chr{cp}), D.resto_nome(t), caracteres)))

law ascii_e_codigo_valido:
  for +cp: U32
  for ascii: {U32.is_lt(cp, 128) == True{} : Bool}
  {B.codigo_valido(cp) == True{} : Bool}
def ascii_e_codigo_valido(cp, ascii):
  Equal.trans(Bool, B.codigo_valido(cp), D.escalar_valido(cp), True{},
    U.predicados_unicode_concordam(cp), U.ascii_e_escalar(cp, ascii))

law texto_ascii_e_valido:
  for +s: String
  for +ascii: {texto_ascii(s) == True{} : Bool}
  {B.texto_valido(s) == True{} : Bool}
def texto_ascii_e_valido(s, ascii):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+cp}, +t}:
      F.e_booleano_intro(B.codigo_valido(cp), B.texto_valido(t),
        ascii_e_codigo_valido(cp, F.e_booleano_esquerda(U32.is_lt(cp, 128), texto_ascii(t), ascii)),
        texto_ascii_e_valido(t, F.e_booleano_direita(U32.is_lt(cp, 128), texto_ascii(t), ascii)))

law codigo_ascii_emite_um_octeto:
  for +cp: U32
  for ascii: {U32.is_lt(cp, 128) == True{} : Bool}
  {B.utf8_codigo(cp) == Con{cp, Nil{}} : List<&2, U32>}
def codigo_ascii_emite_um_octeto(cp, ascii):
  %Equal.sym(Bool, U32.is_lt(cp, 128), True{}, ascii) :
    {B.utf8_codigo_emitir(cp, _, U32.is_lt(cp, 2048), U32.is_lt(cp, 65536)) == Con{cp, Nil{}} : List<&2, U32>}
  {==}

law texto_ascii_tem_um_octeto_por_caractere:
  for +s: String
  for +ascii: {texto_ascii(s) == True{} : Bool}
  {B.comprimento(B.utf8(s)) == String.length(s) : Nat}
def texto_ascii_tem_um_octeto_por_caractere(s, ascii):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+cp}, +t}:
      %Equal.sym(List<&2, U32>, B.utf8_codigo(cp), Con{cp, Nil{}},
        codigo_ascii_emite_um_octeto(cp, F.e_booleano_esquerda(U32.is_lt(cp, 128), texto_ascii(t), ascii))) :
        {B.comprimento(B.concatenar(_, B.utf8(t))) == 1n+String.length(t) : Nat}
      Equal.cong(Nat, Nat, n => 1n+n, B.comprimento(B.utf8(t)), String.length(t),
        texto_ascii_tem_um_octeto_por_caractere(t,
          F.e_booleano_direita(U32.is_lt(cp, 128), texto_ascii(t), ascii)))

law nome_valido_e_texto_valido:
  for +s: String
  for valido: {D.nome_valido(s) == True{} : Bool}
  {B.texto_valido(s) == True{} : Bool}
def nome_valido_e_texto_valido(s, valido):
  texto_ascii_e_valido(s, nome_valido_e_ascii(s, valido))

law nome_valido_utf8_tem_comprimento_exato:
  for +s: String
  for valido: {D.nome_valido(s) == True{} : Bool}
  {B.comprimento(B.utf8(s)) == String.length(s) : Nat}
def nome_valido_utf8_tem_comprimento_exato(s, valido):
  texto_ascii_tem_um_octeto_por_caractere(s, nome_valido_e_ascii(s, valido))

law nome_valido_tem_ate64_caracteres:
  for +s: String
  for valido: {D.nome_valido(s) == True{} : Bool}
  {Nat.is_le(String.length(s), 64n) == True{} : Bool}
def nome_valido_tem_ate64_caracteres(s, valido):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      F.e_booleano_direita(D.inicio_nome(h) && D.resto_nome(t),
        Nat.is_le(String.length(SCon{h, t}), 64n), valido)

law nome_valido_utf8_tem_ate64_octetos:
  for +s: String
  for +valido: {D.nome_valido(s) == True{} : Bool}
  {Nat.is_le(B.comprimento(B.utf8(s)), 64n) == True{} : Bool}
def nome_valido_utf8_tem_ate64_octetos(s, valido):
  Equal.trans(Bool, Nat.is_le(B.comprimento(B.utf8(s)), 64n), Nat.is_le(String.length(s), 64n), True{},
    Equal.cong(Nat, Bool, n => Nat.is_le(n, 64n), B.comprimento(B.utf8(s)), String.length(s),
      nome_valido_utf8_tem_comprimento_exato(s, valido)),
    nome_valido_tem_ate64_caracteres(s, valido))
