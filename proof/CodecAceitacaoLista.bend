# Segmentacao integral do payload REAL de uma lista aceita.
# O combustivel e apenas um majorante matematico do comprimento restante.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecPercurso.bend as R
import ./CodecAridades.bend as A
import ./CodecLimitesSequencias.bend as S
import ./CodecAceitacaoPrefixo.bend as X
import ./CodecAceitacaoFilhos.bend as H

type Segmentacao<-bs: List<&2, U32>, -inicio: C.Maquina, -v: D.Valor, -max: Nat> is Type:
  Segmentacao{xs: List<&2, S.ValorSegmentado>,
    bytes: {bs == S.bytes_valores(xs) : List<&2, U32>},
    entrega: {A.entregar_valores(S.valores(xs), inicio) == C.Pronto{v} : C.Maquina},
    filhos: H.FilhosLidos(xs, max)}

# A emissao em uma lista raiz conserva exatamente estes dois estados.
type EstadoLista is Data:
  Lendo{ultimo: Bool, restantes: B.Numero64, invertidos: List<&2, D.Valor>}
  Terminada{valor: D.Valor}

def maquina_lista(e: EstadoLista) -> C.Maquina:
  match e:
    case Lendo{u, q, xs}:
      C.Tag{C.Lista{u, q, xs, C.Raiz{}}}
    case Terminada{v}:
      C.Pronto{v}

def pronto_com_sufixo_impossivel(+b: U32, +bs: List<&2, U32>,
  +corpo: B.Numero64, +teto: B.Numero64, +w: D.Valor, -v: D.Valor,
  aceito: {R.maquina(R.executar(Con{b, bs}, R.Quadro{corpo, teto, C.Pronto{w}})) == C.Pronto{v} : C.Maquina}) -> Empty:
  R.entrada_nao_decodificada(v,
    Equal.trans(C.Resultado, C.Entrada{}, R.finalizar_quadro(R.executar(Con{b, bs}, R.Quadro{corpo, teto, C.Pronto{w}})), C.Decodificado{v},
      Equal.trans(C.Resultado, C.Entrada{}, C.percorrer(Con{b, bs}, corpo, teto, C.Pronto{w}),
        R.finalizar_quadro(R.executar(Con{b, bs}, R.Quadro{corpo, teto, C.Pronto{w}})),
        Equal.sym(C.Resultado, C.percorrer(Con{b, bs}, corpo, teto, C.Pronto{w}), C.Entrada{},
          R.pronto_recusa_qualquer_octeto_extra(b, bs, corpo, teto, w)),
        R.percurso_e_execucao_integral(Con{b, bs}, R.Quadro{corpo, teto, C.Pronto{w}})),
      Equal.cong(C.Maquina, C.Resultado, m => C.finalizar(m),
        R.maquina(R.executar(Con{b, bs}, R.Quadro{corpo, teto, C.Pronto{w}})), C.Pronto{v}, aceito)))

def anexar_filho_lido(+bs: List<&2, U32>, +pre: List<&2, U32>, +suf: List<&2, U32>,
  +fora: C.Pilha, +h: D.Valor, -v: D.Valor, +max: Nat,
  bytes: {bs == B.concatenar(pre, suf) : List<&2, U32>},
  filho: H.FilhoLido<h, pre, max>,
  cauda: Segmentacao<suf, C.emitir(fora, h), v, max>) ->
  Segmentacao<bs, C.Tag{fora}, v, max>:
  match cauda:
    case Segmentacao{+xs, resto_bytes, entrega, filhos}:
      Segmentacao{Con{S.ValorSegmentado{h, pre}, xs},
        Equal.trans(List<&2, U32>, bs, B.concatenar(pre, suf), B.concatenar(pre, S.bytes_valores(xs)), bytes,
          Equal.cong(List<&2, U32>, List<&2, U32>, t => B.concatenar(pre, t), suf, S.bytes_valores(xs), resto_bytes)),
        entrega, L.Ambos{filho, filhos}}

def continuar_corte_lista(+n: Nat, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  +ultimo: Bool, +q: B.Numero64, +invertidos: List<&2, D.Valor>, -v: D.Valor, +max: Nat,
  limite_n: {Nat.is_le(B.comprimento(bs), 1n+n) == True{} : Bool},
  limite_max: {Nat.is_le(B.comprimento(bs), max) == True{} : Bool},
  corte: X.Corte<bs, corpo, teto, C.Tag{C.Raiz{}}, C.Lista{ultimo, q, invertidos, C.Raiz{}}, v>,
  continuar: @suf: List<&2, U32> -> @cf: B.Numero64 -> @tf: B.Numero64 -> @estado: EstadoLista ->
    {Nat.is_le(B.comprimento(suf), n) == True{} : Bool} ->
    {Nat.is_le(B.comprimento(suf), max) == True{} : Bool} ->
    {R.maquina(R.executar(suf, R.Quadro{cf, tf, maquina_lista(estado)})) == C.Pronto{v} : C.Maquina} ->
    Segmentacao<suf, maquina_lista(estado), v, max>) ->
  Segmentacao<bs, C.Tag{C.Lista{ultimo, q, invertidos, C.Raiz{}}}, v, max>:
  match ultimo corte:
    case True{} X.Corte{+pre, +suf, +h, +cf, +tf, +bytes, local, real, restante}:
      +fora = {C.Lista{True{}, q, invertidos, C.Raiz{}} : C.Pilha}
      +local_aceito = Equal.cong(R.Quadro, C.Maquina, quadro => R.maquina(quadro),
        X.executar_local(pre, fora, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}}), R.Quadro{cf, tf, C.Pronto{h}}, local)
      +corte_max = H.limite_de_bytes_iguais(bs, B.concatenar(pre, suf), max, bytes, limite_max)
      anexar_filho_lido(bs, pre, suf, fora, h, v, max, bytes,
        H.FilhoLido{corpo, teto, fora, local_aceito, H.limite_prefixo(pre, suf, max, corte_max)},
        continuar(suf, cf, tf,
          Terminada{C.montar_lista(Con{h, invertidos}, D.VListaVazia{})},
          H.sufixo_apos_prefixo_positivo(pre, suf, n,
            H.tag_raiz_local_aceito_tem_bytes(pre, fora, corpo, teto, h, local_aceito),
            H.limite_de_bytes_iguais(bs, B.concatenar(pre, suf), 1n+n, bytes, limite_n)),
          H.limite_sufixo(pre, suf, max, corte_max), restante))
    case False{} X.Corte{+pre, +suf, +h, +cf, +tf, +bytes, local, real, restante}:
      +fora = {C.Lista{False{}, q, invertidos, C.Raiz{}} : C.Pilha}
      +local_aceito = Equal.cong(R.Quadro, C.Maquina, quadro => R.maquina(quadro),
        X.executar_local(pre, fora, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}}), R.Quadro{cf, tf, C.Pronto{h}}, local)
      +corte_max = H.limite_de_bytes_iguais(bs, B.concatenar(pre, suf), max, bytes, limite_max)
      anexar_filho_lido(bs, pre, suf, fora, h, v, max, bytes,
        H.FilhoLido{corpo, teto, fora, local_aceito, H.limite_prefixo(pre, suf, max, corte_max)},
        continuar(suf, cf, tf,
          Lendo{C.um64(q), C.diminuir64(q), Con{h, invertidos}},
          H.sufixo_apos_prefixo_positivo(pre, suf, n,
            H.tag_raiz_local_aceito_tem_bytes(pre, fora, corpo, teto, h, local_aceito),
            H.limite_de_bytes_iguais(bs, B.concatenar(pre, suf), 1n+n, bytes, limite_n)),
          H.limite_sufixo(pre, suf, max, corte_max), restante))

law extrair_lista_por_combustivel:
  for n: Nat
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +estado: EstadoLista
  for -v: D.Valor
  for +max: Nat
  for limite_n: {Nat.is_le(B.comprimento(bs), n) == True{} : Bool}
  for limite_max: {Nat.is_le(B.comprimento(bs), max) == True{} : Bool}
  for aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, maquina_lista(estado)})) == C.Pronto{v} : C.Maquina}
  Segmentacao<bs, maquina_lista(estado), v, max>
def extrair_lista_por_combustivel(n, bs, corpo, teto, estado, v, max, limite_n, limite_max, aceito):
  match n bs estado:
    case _ Nil{} Lendo{u, q, xs}:
      L.ex_falso(Segmentacao<Nil{}, maquina_lista(estado), v, max>,
        F.falso_nao_verdadeiro(Equal.cong(C.Maquina, Bool, m => X.e_pronto(m), maquina_lista(estado), C.Pronto{v}, aceito)))
    case _ Nil{} Terminada{w}:
      Segmentacao{Nil{}, {==}, aceito, Unit{}}
    case 0n Con{b, t} _:
      F.absurdo_booleano(Segmentacao<bs, maquina_lista(estado), v, max>, limite_n)
    case 1n+ +menor Con{b, t} Terminada{+w}:
      L.ex_falso(Segmentacao<bs, C.Pronto{w}, v, max>, pronto_com_sufixo_impossivel(b, t, corpo, teto, w, v, aceito))
    case 1n+ +menor Con{b, t} Lendo{+u, +q, +invertidos}:
      continuar_corte_lista(menor, bs, corpo, teto, u, q, invertidos, v, max, limite_n, limite_max,
        X.execucao_real_aceita_extrai_a_primeira_emissao(bs, corpo, teto, C.Tag{C.Raiz{}},
          C.Lista{u, q, invertidos, C.Raiz{}}, v, Unit{}, aceito),
        suf => cf => tf => proximo => ln => lm => aceito_resto =>
          extrair_lista_por_combustivel(menor, suf, cf, tf, proximo, v, max, ln, lm, aceito_resto))

def extrair_abertura_lista(vazio: Bool, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  +q: B.Numero64, -v: D.Valor,
  aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.abrir_variavel(vazio, C.ContaLista{}, q, C.Raiz{})})) == C.Pronto{v} : C.Maquina}) ->
  Segmentacao<bs, C.abrir_variavel(vazio, C.ContaLista{}, q, C.Raiz{}), v, B.comprimento(bs)>:
  match vazio:
    case True{}:
      extrair_lista_por_combustivel(B.comprimento(bs), bs, corpo, teto, Terminada{D.VListaVazia{}}, v, B.comprimento(bs),
        S.limite_reflexivo(B.comprimento(bs)), S.limite_reflexivo(B.comprimento(bs)), aceito)
    case False{}:
      extrair_lista_por_combustivel(B.comprimento(bs), bs, corpo, teto, Lendo{C.um64(q), C.diminuir64(q), Nil{}}, v, B.comprimento(bs),
        S.limite_reflexivo(B.comprimento(bs)), S.limite_reflexivo(B.comprimento(bs)), aceito)

law lista_aceita_extrai_todos_os_filhos:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +q: B.Numero64
  for -v: D.Valor
  for aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.abrir_variavel(C.zero64(q), C.ContaLista{}, q, C.Raiz{})})) == C.Pronto{v} : C.Maquina}
  Segmentacao<bs, C.abrir_variavel(C.zero64(q), C.ContaLista{}, q, C.Raiz{}), v, B.comprimento(bs)>
def lista_aceita_extrai_todos_os_filhos(bs, corpo, teto, q, v, aceito):
  extrair_abertura_lista(C.zero64(q), bs, corpo, teto, q, v, aceito)
