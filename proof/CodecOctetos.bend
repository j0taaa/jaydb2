# Todo resultado do encoder ORIGINAL contem apenas octetos. Inclui falha
# por Unicode, forma impropria e contagem irrepresentavel, sem truncamento.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ./Fundamentos.bend as F
import ./CodecInteiros.bend as J
import ./CodecUTF8InversaOctetos.bend as U

def OctetosOpcionais(m: Maybe<&2, List<&2, U32>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{bs}:
      {B.octetos_validos(bs) == True{} : Bool}

def ParcialOctetos(p: P.Parcial) -> Type:
  match p:
    case P.Impossivel{}:
      Unit
    case P.Atomo{bs}:
      {B.octetos_validos(bs) == True{} : Bool}
    case P.Lista{n, bs}:
      {B.octetos_validos(bs) == True{} : Bool}
    case P.Registro{n, bs}:
      {B.octetos_validos(bs) == True{} : Bool}

law numero64_opcional_so_emite_octetos:
  for n: Maybe<&2, B.Numero64>
  OctetosOpcionais(B.numero64_bytes(n))
def numero64_opcional_so_emite_octetos(n):
  match n:
    case None{}:
      Unit{}
    case Some{B.Numero64{a, b}}:
      J.be64_so_emite_octetos(a, b)

law prefixar_preserva_octetos:
  for +tag: U32
  for +h: Maybe<&2, List<&2, U32>>
  for +bs: List<&2, U32>
  for vt: {U32.is_le(tag, 255) == True{} : Bool}
  for vh: OctetosOpcionais(h)
  for vb: {B.octetos_validos(bs) == True{} : Bool}
  OctetosOpcionais(P.prefixar_tamanho(tag, h, bs))
def prefixar_preserva_octetos(tag, h, bs, vt, vh, vb):
  match h:
    case None{}:
      Unit{}
    case Some{+cabecalho}:
      F.e_booleano_intro(U32.is_le(tag, 255), B.octetos_validos(B.concatenar(cabecalho, bs)), vt,
        J.concatenar_preserva_octetos(cabecalho, bs, vh, vb))

law finalizar_preserva_octetos:
  for +p: P.Parcial
  for octetos: ParcialOctetos(p)
  OctetosOpcionais(P.finalizar(p))
def finalizar_preserva_octetos(p, octetos):
  match p:
    case P.Impossivel{}:
      Unit{}
    case P.Atomo{bs}:
      octetos
    case P.Lista{+n, +bs}:
      prefixar_preserva_octetos(5, B.comprimento64(n), bs, {==}, numero64_opcional_so_emite_octetos(B.nat64(n)), octetos)
    case P.Registro{+n, +bs}:
      prefixar_preserva_octetos(6, B.comprimento64(n), bs, {==}, numero64_opcional_so_emite_octetos(B.nat64(n)), octetos)

def texto_casos_preserva_octetos(valido: Bool, +s: String,
  caso: {B.texto_valido(s) == valido : Bool}) -> OctetosOpcionais(P.texto_casos(valido, B.utf8(s))):
  match valido:
    case False{}:
      Unit{}
    case True{}:
      prefixar_preserva_octetos(4, B.comprimento64(B.comprimento(B.utf8(s))), B.utf8(s), {==},
        numero64_opcional_so_emite_octetos(B.nat64(B.comprimento(B.utf8(s)))), U.utf8_texto_valido_emite_octetos(s, caso))

law texto_so_emite_octetos:
  for +s: String
  OctetosOpcionais(P.texto(s))
def texto_so_emite_octetos(s):
  texto_casos_preserva_octetos(B.texto_valido(s), s, {==})

def atomo_opcional_preserva_octetos(+m: Maybe<&2, List<&2, U32>>,
  octetos: OctetosOpcionais(m)) -> ParcialOctetos(P.atomo_opcional(m)):
  match m:
    case None{}:
      Unit{}
    case Some{bs}:
      octetos

def lista_casos_preserva_octetos(+h: Maybe<&2, List<&2, U32>>, +t: P.Parcial,
  vh: OctetosOpcionais(h), vt: ParcialOctetos(t)) -> ParcialOctetos(P.lista_casos(h, t)):
  match h t:
    case None{} _:
      Unit{}
    case Some{bs} P.Impossivel{}:
      Unit{}
    case Some{bs} P.Atomo{ts}:
      Unit{}
    case Some{+bs} P.Lista{n, +ts}:
      J.concatenar_preserva_octetos(bs, ts, vh, vt)
    case Some{bs} P.Registro{n, ts}:
      Unit{}

def registro_casos_preserva_octetos(+nome: Maybe<&2, List<&2, U32>>, +v: Maybe<&2, List<&2, U32>>, +r: P.Parcial,
  vn: OctetosOpcionais(nome), vv: OctetosOpcionais(v), vr: ParcialOctetos(r)) -> ParcialOctetos(P.registro_casos(nome, v, r)):
  match nome v r:
    case None{} _ _:
      Unit{}
    case Some{bs} None{} _:
      Unit{}
    case Some{bs} Some{vs} P.Impossivel{}:
      Unit{}
    case Some{bs} Some{vs} P.Atomo{rs}:
      Unit{}
    case Some{bs} Some{vs} P.Lista{n, rs}:
      Unit{}
    case Some{+bs} Some{+vs} P.Registro{n, +rs}:
      J.concatenar_preserva_octetos(bs, B.concatenar(vs, rs), vn, J.concatenar_preserva_octetos(vs, rs, vv, vr))

def booleano_so_emite_octetos(b: Bool) -> ParcialOctetos(P.booleano(b)):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law codificar_parcial_so_emite_octetos:
  for +v: D.Valor
  ParcialOctetos(P.codificar_parcial(v))
def codificar_parcial_so_emite_octetos(v):
  match v:
    case D.VAusente{}:
      {==}
    case D.VBool{b}:
      booleano_so_emite_octetos(b)
    case D.VInt{+a, +b}:
      J.be64_so_emite_octetos(a, b)
    case D.VTexto{+s}:
      atomo_opcional_preserva_octetos(P.texto(s), texto_so_emite_octetos(s))
    case D.VListaVazia{}:
      {==}
    case D.VLista{+h, +t}:
      lista_casos_preserva_octetos(P.finalizar(P.codificar_parcial(h)), P.codificar_parcial(t),
        finalizar_preserva_octetos(P.codificar_parcial(h), codificar_parcial_so_emite_octetos(h)), codificar_parcial_so_emite_octetos(t))
    case D.VRegistroVazio{}:
      {==}
    case D.VRegistro{+n, +v, +r}:
      registro_casos_preserva_octetos(P.texto(n), P.finalizar(P.codificar_parcial(v)), P.codificar_parcial(r), texto_so_emite_octetos(n),
        finalizar_preserva_octetos(P.codificar_parcial(v), codificar_parcial_so_emite_octetos(v)), codificar_parcial_so_emite_octetos(r))

def codificar_casos_preserva_octetos(valido: Bool, +m: Maybe<&2, List<&2, U32>>, octetos: OctetosOpcionais(m)) -> OctetosOpcionais(P.codificar_casos(valido, m)):
  match valido:
    case False{}:
      Unit{}
    case True{}:
      octetos

law codificar_so_emite_octetos:
  for +v: D.Valor
  OctetosOpcionais(P.codificar(v))
def codificar_so_emite_octetos(v):
  codificar_casos_preserva_octetos(D.valor_valido(v), P.finalizar(P.codificar_parcial(v)),
    finalizar_preserva_octetos(P.codificar_parcial(v), codificar_parcial_so_emite_octetos(v)))

def resultado_aceito_tem_octetos(+m: Maybe<&2, List<&2, U32>>, -bs: List<&2, U32>,
  octetos: OctetosOpcionais(m), aceito: {m == Some{bs} : Maybe<&2, List<&2, U32>>}) -> {B.octetos_validos(bs) == True{} : Bool}:
  match m:
    case None{}:
      L.ex_falso({B.octetos_validos(bs) == True{} : Bool}, F.nenhum_nao_algum(List<&2, U32>, bs, aceito))
    case Some{+bytes}:
      %F.algum_injetivo(List<&2, U32>, bytes, bs, aceito) : {B.octetos_validos(_) == True{} : Bool}
      octetos

law qualquer_codificacao_so_emite_octetos:
  for +v: D.Valor
  for -bs: List<&2, U32>
  for codificado: P.Codificacao(v, bs)
  {B.octetos_validos(bs) == True{} : Bool}
def qualquer_codificacao_so_emite_octetos(v, bs, codificado):
  resultado_aceito_tem_octetos(P.codificar(v), bs, codificar_so_emite_octetos(v), codificado)
