# Limites dos segmentos produzidos pelo codificador parcial REAL.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ./Fundamentos.bend as F
import ./CodecConteudo.bend as G
import ./CodecTamanhos.bend as T
import ./CodecLimitesNomes.bend as N
import ./CodecLimitesSequencias.bend as S

def ParcialLimitado(p: P.Parcial) -> Type:
  match p:
    case P.Impossivel{}:
      Unit
    case P.Atomo{bs}:
      G.NaoVazio(bs)
    case P.Lista{n, bs}:
      {Nat.is_le(n, B.comprimento(bs)) == True{} : Bool}
    case P.Registro{n, bs}:
      {Nat.is_le(Nat.mul(11n, n), B.comprimento(bs)) == True{} : Bool}

law finalizar_preserva_tag:
  for p: P.Parcial
  for tag: T.ParcialComTag(p)
  T.ResultadoComTag(P.finalizar(p))
def finalizar_preserva_tag(p, tag):
  match p:
    case P.Impossivel{}:
      Unit{}
    case P.Atomo{bs}:
      tag
    case P.Lista{n, bs}:
      T.prefixar_tamanho_sempre_insere_tag(5, B.comprimento64(n), bs)
    case P.Registro{n, bs}:
      T.prefixar_tamanho_sempre_insere_tag(6, B.comprimento64(n), bs)

law atomo_opcional_limitado:
  for m: Maybe<&2, List<&2, U32>>
  for tag: T.ResultadoComTag(m)
  ParcialLimitado(P.atomo_opcional(m))
def atomo_opcional_limitado(m, tag):
  match m:
    case None{}:
      Unit{}
    case Some{bs}:
      tag

law booleano_limitado:
  for b: Bool
  ParcialLimitado(P.booleano(b))
def booleano_limitado(b):
  match b:
    case False{}:
      Unit{}
    case True{}:
      Unit{}

law lista_casos_limitados:
  for h: Maybe<&2, List<&2, U32>>
  for t: P.Parcial
  for tag_h: T.ResultadoComTag(h)
  for limite_t: ParcialLimitado(t)
  ParcialLimitado(P.lista_casos(h, t))
def lista_casos_limitados(h, t, tag_h, limite_t):
  match h t:
    case None{} _:
      Unit{}
    case Some{bs} P.Impossivel{}:
      Unit{}
    case Some{bs} P.Atomo{resto}:
      Unit{}
    case Some{+bs} P.Lista{+n, +resto}:
      S.concatenar_segmentos_preserva_soma_dos_limites(bs, resto, 1n, n,
        T.bytes_nao_vazios_tem_pelo_menos_um_octeto(bs, tag_h), limite_t)
    case Some{bs} P.Registro{n, resto}:
      Unit{}

law registro_casos_limitados:
  for +nome: String
  for nome_bytes: Maybe<&2, List<&2, U32>>
  for valor_bytes: Maybe<&2, List<&2, U32>>
  for r: P.Parcial
  for valido: {D.nome_valido(nome) == True{} : Bool}
  for texto: {P.texto(nome) == nome_bytes : Maybe<&2, List<&2, U32>>}
  for tag_valor: T.ResultadoComTag(valor_bytes)
  for limite_r: ParcialLimitado(r)
  ParcialLimitado(P.registro_casos(nome_bytes, valor_bytes, r))
def registro_casos_limitados(nome, nome_bytes, valor_bytes, r, valido, texto, tag_valor, limite_r):
  match nome_bytes valor_bytes r:
    case None{} _ _:
      Unit{}
    case Some{nb} None{} _:
      Unit{}
    case Some{nb} Some{vb} P.Impossivel{}:
      Unit{}
    case Some{nb} Some{vb} P.Atomo{resto}:
      Unit{}
    case Some{nb} Some{vb} P.Lista{n, resto}:
      Unit{}
    case Some{+nb} Some{+vb} P.Registro{+n, +resto}:
      %Equal.sym(Nat, Nat.mul(11n, 1n+n), Nat.add(11n, Nat.mul(11n, n)), S.multiplicar_sucessor_direito(11n, n)) :
        {Nat.is_le(_, B.comprimento(B.concatenar(nb, B.concatenar(vb, resto)))) == True{} : Bool}
      S.concatenar_segmentos_preserva_soma_dos_limites(nb, B.concatenar(vb, resto), 10n, Nat.add(1n, Nat.mul(11n, n)),
        N.nome_canonico_exige_dez_octetos(nome, nb, valido, texto),
        S.concatenar_segmentos_preserva_soma_dos_limites(vb, resto, 1n, Nat.mul(11n, n),
          T.bytes_nao_vazios_tem_pelo_menos_um_octeto(vb, tag_valor), limite_r))

law codificacao_parcial_valida_respeita_limites:
  for +v: D.Valor
  for +valido: {D.valor_valido(v) == True{} : Bool}
  ParcialLimitado(P.codificar_parcial(v))
def codificacao_parcial_valida_respeita_limites(v, valido):
  match v:
    case D.VAusente{}:
      Unit{}
    case D.VBool{b}:
      booleano_limitado(b)
    case D.VInt{alto, baixo}:
      Unit{}
    case D.VTexto{+s}:
      atomo_opcional_limitado(P.texto(s), T.texto_casos_sempre_insere_tag(B.texto_valido(s), B.utf8(s)))
    case D.VListaVazia{}:
      {==}
    case D.VLista{+h, +t}:
      lista_casos_limitados(P.finalizar(P.codificar_parcial(h)), P.codificar_parcial(t),
        finalizar_preserva_tag(P.codificar_parcial(h), T.codificacao_parcial_nunca_perde_tag(h)),
        codificacao_parcial_valida_respeita_limites(t,
          F.e_booleano_direita(D.valor_valido(h) && D.eh_lista(t), D.valor_valido(t), valido)))
    case D.VRegistroVazio{}:
      {==}
    case D.VRegistro{+nome, +x, +r}:
      registro_casos_limitados(nome, P.texto(nome), P.finalizar(P.codificar_parcial(x)), P.codificar_parcial(r),
        F.e_booleano_esquerda(D.nome_valido(nome), D.valor_valido(x),
          F.e_booleano_esquerda(D.nome_valido(nome) && D.valor_valido(x), D.registro_depois(r, nome),
            F.e_booleano_esquerda(D.nome_valido(nome) && D.valor_valido(x) && D.registro_depois(r, nome), D.valor_valido(r), valido))),
        {==}, finalizar_preserva_tag(P.codificar_parcial(x), T.codificacao_parcial_nunca_perde_tag(x)),
        codificacao_parcial_valida_respeita_limites(r,
          F.e_booleano_direita(D.nome_valido(nome) && D.valor_valido(x) && D.registro_depois(r, nome), D.valor_valido(r), valido)))

law conteudo_lista_canonica_exige_um_octeto_por_elemento:
  for +v: D.Valor
  for +n: Nat
  for +conteudo: List<&2, U32>
  for valido: {D.valor_valido(v) == True{} : Bool}
  for parcial: {P.codificar_parcial(v) == P.Lista{n, conteudo} : P.Parcial}
  {Nat.is_le(n, B.comprimento(conteudo)) == True{} : Bool}
def conteudo_lista_canonica_exige_um_octeto_por_elemento(v, n, conteudo, valido, parcial):
  %parcial : ParcialLimitado(_)
  codificacao_parcial_valida_respeita_limites(v, valido)

law conteudo_registro_canonico_exige_onze_octetos_por_campo:
  for +v: D.Valor
  for +n: Nat
  for +conteudo: List<&2, U32>
  for valido: {D.valor_valido(v) == True{} : Bool}
  for parcial: {P.codificar_parcial(v) == P.Registro{n, conteudo} : P.Parcial}
  {Nat.is_le(Nat.mul(11n, n), B.comprimento(conteudo)) == True{} : Bool}
def conteudo_registro_canonico_exige_onze_octetos_por_campo(v, n, conteudo, valido, parcial):
  %parcial : ParcialLimitado(_)
  codificacao_parcial_valida_respeita_limites(v, valido)

law codificacao_lista_exige_cabecalho_e_elementos:
  for +v: D.Valor
  for +n: Nat
  for +conteudo: List<&2, U32>
  for +bs: List<&2, U32>
  for valido: {D.valor_valido(v) == True{} : Bool}
  for +parcial: {P.codificar_parcial(v) == P.Lista{n, conteudo} : P.Parcial}
  for codificado: P.Codificacao(v, bs)
  {Nat.is_le(Nat.add(9n, n), B.comprimento(bs)) == True{} : Bool}
def codificacao_lista_exige_cabecalho_e_elementos(v, n, conteudo, bs, valido, parcial, codificado):
  %Equal.sym(Nat, B.comprimento(bs), Nat.add(9n, B.comprimento(conteudo)),
      N.prefixo_numero64_tem_nove_octetos_adicionais(B.nat64(n), 5, conteudo, bs,
        (%parcial :
          {P.finalizar(_) == Some{bs} : Maybe<&2, List<&2, U32>>}
          T.casos_aceitos_preservam_resultado(D.valor_valido(v), P.finalizar(P.codificar_parcial(v)), bs, codificado)))) :
    {Nat.is_le(Nat.add(9n, n), _) == True{} : Bool}
  N.somar_preserva_limites(9n, n, 9n, B.comprimento(conteudo), {==},
    conteudo_lista_canonica_exige_um_octeto_por_elemento(v, n, conteudo, valido, parcial))

law codificacao_registro_exige_cabecalho_e_campos:
  for +v: D.Valor
  for +n: Nat
  for +conteudo: List<&2, U32>
  for +bs: List<&2, U32>
  for valido: {D.valor_valido(v) == True{} : Bool}
  for +parcial: {P.codificar_parcial(v) == P.Registro{n, conteudo} : P.Parcial}
  for codificado: P.Codificacao(v, bs)
  {Nat.is_le(Nat.add(9n, Nat.mul(11n, n)), B.comprimento(bs)) == True{} : Bool}
def codificacao_registro_exige_cabecalho_e_campos(v, n, conteudo, bs, valido, parcial, codificado):
  %Equal.sym(Nat, B.comprimento(bs), Nat.add(9n, B.comprimento(conteudo)),
      N.prefixo_numero64_tem_nove_octetos_adicionais(B.nat64(n), 6, conteudo, bs,
        (%parcial :
          {P.finalizar(_) == Some{bs} : Maybe<&2, List<&2, U32>>}
          T.casos_aceitos_preservam_resultado(D.valor_valido(v), P.finalizar(P.codificar_parcial(v)), bs, codificado)))) :
    {Nat.is_le(Nat.add(9n, Nat.mul(11n, n)), _) == True{} : Bool}
  N.somar_preserva_limites(9n, Nat.mul(11n, n), 9n, B.comprimento(conteudo), {==},
    conteudo_registro_canonico_exige_onze_octetos_por_campo(v, n, conteudo, valido, parcial))
