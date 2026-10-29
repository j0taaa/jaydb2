# Simulacao geral entre o transdutor UTF-8 do parser e o reconhecedor
# original de contrato/Bytes. Nenhuma enumeracao de caracteres/octetos.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C

# O transdutor nunca guarda Continua{0,...}: o ultimo byte produz Caractere.
def UnicodeNormal(u: C.Unicode) -> Type:
  match u:
    case C.Inicio{}:
      Unit
    case C.Continua{0n, cp, minimo}:
      Empty
    case C.Continua{1n+p, cp, minimo}:
      Unit

def EscalarNormal(e: C.Escalar) -> Type:
  match e:
    case C.Parcial{u}:
      UnicodeNormal(u)
    case _:
      Unit

def representar(u: C.Unicode) -> B.Decodificador:
  match u:
    case C.Inicio{}:
      B.Dec{0n, 0, 0}
    case C.Continua{n, cp, minimo}:
      B.Dec{n, cp, minimo}

def espelhar(e: C.Escalar) -> B.Decodificador:
  match e:
    case C.UTFInvalido{}:
      B.Invalido{}
    case C.Caractere{cp}:
      B.Dec{0n, 0, 0}
    case C.Parcial{u}:
      representar(u)

law escalar_conferido_espelha_reconhecedor:
  for ok: Bool
  for cp: U32
  {espelhar(C.escalar_conferido(ok, cp)) == B.selecionar_dec(ok, B.Dec{0n, 0, 0}) : B.Decodificador}
def escalar_conferido_espelha_reconhecedor(ok, cp):
  match ok:
    case False{}:
      {==}
    case True{}:
      {==}

law completar_utf8_espelha_reconhecedor:
  for n: Nat
  for +cp: U32
  for +minimo: U32
  {espelhar(C.completar_utf8(n, cp, minimo)) == B.continuar_fim(n, cp, minimo) : B.Decodificador}
def completar_utf8_espelha_reconhecedor(n, cp, minimo):
  match n:
    case 0n:
      escalar_conferido_espelha_reconhecedor(U32.is_ge(cp, minimo) && B.codigo_valido(cp), cp)
    case 1n+p:
      {==}

law continuar_utf8_espelha_reconhecedor:
  for ok: Bool
  for +n: Nat
  for +cp: U32
  for +minimo: U32
  for +b: U32
  {espelhar(C.continuar_utf8(ok, n, cp, minimo, b)) ==
    B.selecionar_dec(ok, B.continuar_fim(n, (cp * 64 + b - 128 : U32), minimo)) : B.Decodificador}
def continuar_utf8_espelha_reconhecedor(ok, n, cp, minimo, b):
  match ok:
    case False{}:
      {==}
    case True{}:
      completar_utf8_espelha_reconhecedor(n, (cp * 64 + b - 128 : U32), minimo)

law iniciar_utf8_espelha_reconhecedor:
  for ascii: Bool
  for dois: Bool
  for tres: Bool
  for quatro: Bool
  for +b: U32
  {espelhar(C.iniciar_utf8(ascii, dois, tres, quatro, b)) == B.iniciar_codigo(b, ascii, dois, tres, quatro) : B.Decodificador}
def iniciar_utf8_espelha_reconhecedor(ascii, dois, tres, quatro, b):
  match ascii dois tres quatro:
    case True{} _ _ _:
      {==}
    case False{} True{} _ _:
      {==}
    case False{} False{} True{} _:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{}:
      {==}

law passo_utf8_espelha_reconhecedor_original:
  for +u: C.Unicode
  for +b: U32
  for normal: UnicodeNormal(u)
  {espelhar(C.passo_utf8(u, b)) == B.passo(representar(u), b) : B.Decodificador}
def passo_utf8_espelha_reconhecedor_original(u, b, normal):
  match u:
    case C.Inicio{}:
      iniciar_utf8_espelha_reconhecedor(U32.is_lt(b, 128), U32.is_ge(b, 194) && U32.is_le(b, 223), U32.is_ge(b, 224) && U32.is_le(b, 239), U32.is_ge(b, 240) && U32.is_le(b, 244), b)
    case C.Continua{0n, cp, minimo}:
      L.ex_falso({espelhar(C.passo_utf8(C.Continua{0n, cp, minimo}, b)) == B.passo(representar(C.Continua{0n, cp, minimo}), b) : B.Decodificador}, normal)
    case C.Continua{1n+p, +cp, +minimo}:
      continuar_utf8_espelha_reconhecedor(U32.is_ge(b, 128) && U32.is_le(b, 191), p, cp, minimo, b)

def escalar_conferido_normal(ok: Bool, cp: U32) -> EscalarNormal(C.escalar_conferido(ok, cp)):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      Unit{}


law completar_utf8_produz_estado_normal:
  for n: Nat
  for +cp: U32
  for +minimo: U32
  EscalarNormal(C.completar_utf8(n, cp, minimo))
def completar_utf8_produz_estado_normal(n, cp, minimo):
  match n:
    case 0n:
      escalar_conferido_normal(U32.is_ge(cp, minimo) && B.codigo_valido(cp), cp)
    case 1n+p:
      Unit{}

law continuar_utf8_produz_estado_normal:
  for ok: Bool
  for +n: Nat
  for +cp: U32
  for +minimo: U32
  for +b: U32
  EscalarNormal(C.continuar_utf8(ok, n, cp, minimo, b))
def continuar_utf8_produz_estado_normal(ok, n, cp, minimo, b):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      completar_utf8_produz_estado_normal(n, (cp * 64 + b - 128 : U32), minimo)

law iniciar_utf8_produz_estado_normal:
  for ascii: Bool
  for dois: Bool
  for tres: Bool
  for quatro: Bool
  for b: U32
  EscalarNormal(C.iniciar_utf8(ascii, dois, tres, quatro, b))
def iniciar_utf8_produz_estado_normal(ascii, dois, tres, quatro, b):
  match ascii dois tres quatro:
    case True{} _ _ _:
      Unit{}
    case False{} True{} _ _:
      Unit{}
    case False{} False{} True{} _:
      Unit{}
    case False{} False{} False{} True{}:
      Unit{}
    case False{} False{} False{} False{}:
      Unit{}

law passo_utf8_produz_estado_normal:
  for u: C.Unicode
  for +b: U32
  EscalarNormal(C.passo_utf8(u, b))
def passo_utf8_produz_estado_normal(u, b):
  match u:
    case C.Inicio{}:
      iniciar_utf8_produz_estado_normal(U32.is_lt(b, 128), U32.is_ge(b, 194) && U32.is_le(b, 223), U32.is_ge(b, 224) && U32.is_le(b, 239), U32.is_ge(b, 240) && U32.is_le(b, 244), b)
    case C.Continua{0n, cp, minimo}:
      Unit{}
    case C.Continua{1n+p, cp, minimo}:
      continuar_utf8_produz_estado_normal(U32.is_ge(b, 128) && U32.is_le(b, 191), p, cp, minimo, b)

# Executa a mesma transducao, mantendo o texto, mas sem o contador externo.
# Esta maquina auxiliar permite separar a inversao de UTF-8 da prova u64.
type Texto is Data:
  TextoInvalido{}
  Lendo{unicode: C.Unicode, invertido: String}

def juntar(e: C.Escalar, invertido: String) -> Texto:
  match e:
    case C.UTFInvalido{}:
      TextoInvalido{}
    case C.Caractere{cp}:
      Lendo{C.Inicio{}, SCon{Chr{cp}, invertido}}
    case C.Parcial{u}:
      Lendo{u, invertido}

def passo_texto(t: Texto, b: U32) -> Texto:
  match t:
    case TextoInvalido{}:
      TextoInvalido{}
    case Lendo{u, invertido}:
      juntar(C.passo_utf8(u, b), invertido)

def TextoNormal(t: Texto) -> Type:
  match t:
    case TextoInvalido{}:
      Unit
    case Lendo{u, invertido}:
      UnicodeNormal(u)

def representar_texto(t: Texto) -> B.Decodificador:
  match t:
    case TextoInvalido{}:
      B.Invalido{}
    case Lendo{u, invertido}:
      representar(u)

def finalizar_texto(t: Texto) -> Maybe<&2, String>:
  match t:
    case TextoInvalido{}:
      None{}
    case Lendo{C.Inicio{}, invertido}:
      Some{String.reverse(invertido)}
    case Lendo{C.Continua{n, cp, minimo}, invertido}:
      None{}

def percorrer_texto(bs: List<&2, U32>, t: Texto) -> Texto:
  match bs:
    case Nil{}:
      t
    case Con{b, resto}:
      percorrer_texto(resto, passo_texto(t, b))

law juntar_espelha_escalar:
  for e: C.Escalar
  for invertido: String
  {representar_texto(juntar(e, invertido)) == espelhar(e) : B.Decodificador}
def juntar_espelha_escalar(e, invertido):
  match e:
    case C.UTFInvalido{}:
      {==}
    case C.Caractere{cp}:
      {==}
    case C.Parcial{u}:
      {==}

law juntar_preserva_normal:
  for +e: C.Escalar
  for invertido: String
  for normal: EscalarNormal(e)
  TextoNormal(juntar(e, invertido))
def juntar_preserva_normal(e, invertido, normal):
  match e:
    case C.UTFInvalido{}:
      Unit{}
    case C.Caractere{cp}:
      Unit{}
    case C.Parcial{u}:
      normal

law passo_texto_preserva_normal:
  for +t: Texto
  for +b: U32
  TextoNormal(passo_texto(t, b))
def passo_texto_preserva_normal(t, b):
  match t:
    case TextoInvalido{}:
      Unit{}
    case Lendo{+u, invertido}:
      juntar_preserva_normal(C.passo_utf8(u, b), invertido, passo_utf8_produz_estado_normal(u, b))

law passo_texto_espelha_reconhecedor:
  for +t: Texto
  for +b: U32
  for normal: TextoNormal(t)
  {representar_texto(passo_texto(t, b)) == B.passo(representar_texto(t), b) : B.Decodificador}
def passo_texto_espelha_reconhecedor(t, b, normal):
  match t:
    case TextoInvalido{}:
      {==}
    case Lendo{+u, invertido}:
      Equal.trans(B.Decodificador, representar_texto(juntar(C.passo_utf8(u, b), invertido)), espelhar(C.passo_utf8(u, b)), B.passo(representar(u), b),
        juntar_espelha_escalar(C.passo_utf8(u, b), invertido), passo_utf8_espelha_reconhecedor_original(u, b, normal))

def tem_texto(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      True{}

law finalizar_texto_espelha_reconhecedor:
  for +t: Texto
  for normal: TextoNormal(t)
  {tem_texto(finalizar_texto(t)) == B.fim(representar_texto(t)) : Bool}
def finalizar_texto_espelha_reconhecedor(t, normal):
  match t:
    case TextoInvalido{}:
      {==}
    case Lendo{C.Inicio{}, invertido}:
      {==}
    case Lendo{C.Continua{0n, cp, minimo}, invertido}:
      L.ex_falso({False{} == True{} : Bool}, normal)
    case Lendo{C.Continua{1n+p, cp, minimo}, invertido}:
      {==}

law transducao_utf8_aceita_exatamente_o_reconhecedor:
  for +bs: List<&2, U32>
  for +t: Texto
  for normal: TextoNormal(t)
  {tem_texto(finalizar_texto(percorrer_texto(bs, t))) == B.utf8_reconhecer(bs, representar_texto(t)) : Bool}
def transducao_utf8_aceita_exatamente_o_reconhecedor(bs, t, normal):
  match bs:
    case Nil{}:
      finalizar_texto_espelha_reconhecedor(t, normal)
    case Con{+b, +resto}:
      %passo_texto_espelha_reconhecedor(t, b, normal) :
        {tem_texto(finalizar_texto(percorrer_texto(resto, passo_texto(t, b)))) == B.utf8_reconhecer(resto, _) : Bool}
      transducao_utf8_aceita_exatamente_o_reconhecedor(resto, passo_texto(t, b), passo_texto_preserva_normal(t, b))

law utf8_do_parser_e_do_contrato_aceitam_os_mesmos_bytes:
  for +bs: List<&2, U32>
  {tem_texto(finalizar_texto(percorrer_texto(bs, Lendo{C.Inicio{}, ""}))) == B.utf8_valido(bs) : Bool}
def utf8_do_parser_e_do_contrato_aceitam_os_mesmos_bytes(bs):
  transducao_utf8_aceita_exatamente_o_reconhecedor(bs, Lendo{C.Inicio{}, ""}, Unit{})
