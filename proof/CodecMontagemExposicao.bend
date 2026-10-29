# Inversao do encoder: a codificacao inteira fornece os segmentos dos
# filhos, a contagem representavel e o cabecalho exato, sem premissas locais.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ./Fundamentos.bend as F
import ./CodecAridades.bend as A
import ./CodecCanonico.bend as K
import ./CodecLimitesSequencias.bend as S
import ./CodecMontagem.bend as M

type Cabecalho<-tag: U32, -n: Nat, -payload: List<&2, U32>, -bs: List<&2, U32>> is Type:
  Cabecalho{numero: B.Numero64,
    medida: {B.nat64(n) == Some{numero} : Maybe<&2, B.Numero64>},
    bytes: {bs == M.prefixo(tag, numero, payload) : List<&2, U32>}}

def expor_medida_variavel(+tag: U32, +n: Nat, +payload: List<&2, U32>, +bs: List<&2, U32>,
  numero: Maybe<&2, B.Numero64>,
  medida: {B.nat64(n) == numero : Maybe<&2, B.Numero64>},
  aceito: {P.prefixar_tamanho(tag, B.numero64_bytes(numero), payload) == Some{bs} : Maybe<&2, List<&2, U32>>}) ->
  Cabecalho<tag, n, payload, bs>:
  match numero:
    case None{}:
      L.ex_falso(Cabecalho<tag, n, payload, bs>, F.nenhum_nao_algum(List<&2, U32>, bs, aceito))
    case Some{B.Numero64{+alto, +baixo}}:
      Cabecalho{B.Numero64{alto, baixo}, medida,
        Equal.sym(List<&2, U32>, M.prefixo(tag, B.Numero64{alto, baixo}, payload), bs,
          F.algum_injetivo(List<&2, U32>, M.prefixo(tag, B.Numero64{alto, baixo}, payload), bs, aceito))}

law campo_variavel_expoe_medida_e_bytes:
  for +tag: U32
  for +n: Nat
  for +payload: List<&2, U32>
  for +bs: List<&2, U32>
  for aceito: {P.campo_variavel(tag, n, payload) == Some{bs} : Maybe<&2, List<&2, U32>>}
  Cabecalho<tag, n, payload, bs>
def campo_variavel_expoe_medida_e_bytes(tag, n, payload, bs, aceito):
  expor_medida_variavel(tag, n, payload, bs, B.nat64(n), {==}, aceito)

# A forma parcial Impossivel nao pode ser finalizada com Some. Sua
# testemunha Unit permite que a inducao estrutural preserve esse fracasso.
type ListaSegmentada<-v: D.Valor, -n: Nat, -payload: List<&2, U32>> is Type:
  ListaSegmentada{segmentos: List<&2, S.ValorSegmentado>,
    valor: {v == A.anexar_lista(S.valores(segmentos), D.VListaVazia{}) : D.Valor},
    canonicos: S.ValoresCanonicos(segmentos),
    quantidade: {S.quantidade_valores(segmentos) == n : Nat},
    bytes: {S.bytes_valores(segmentos) == payload : List<&2, U32>}}

def ParcialLista(v: D.Valor, p: P.Parcial) -> Type:
  match p:
    case P.Impossivel{}:
      Unit
    case P.Lista{n, payload}:
      ListaSegmentada<v, n, payload>
    case _:
      Empty

def expor_cabeca_lista(+h: D.Valor, +t: D.Valor,
  cabeca: Maybe<&2, List<&2, U32>>, cauda: P.Parcial,
  valido: {D.valor_valido(h) == True{} : Bool},
  bytes_cabeca: {P.finalizar(P.codificar_parcial(h)) == cabeca : Maybe<&2, List<&2, U32>>},
  resto: ParcialLista(t, cauda)) -> ParcialLista(D.VLista{h, t}, P.lista_casos(cabeca, cauda)):
  match cabeca cauda:
    case None{} _:
      Unit{}
    case Some{+bs} P.Lista{+n, +payload}:
      match resto:
        case ListaSegmentada{+segmentos, valor, canonicos, quantidade, bytes}:
          ListaSegmentada{Con{S.ValorSegmentado{h, bs}, segmentos},
            Equal.cong(D.Valor, D.Valor, r => D.VLista{h, r}, t, A.anexar_lista(S.valores(segmentos), D.VListaVazia{}), valor),
            L.Ambos{Equal.trans(Maybe<&2, List<&2, U32>>, P.codificar(h), P.finalizar(P.codificar_parcial(h)), Some{bs},
              K.valor_valido_libera_codificacao(h, valido), bytes_cabeca), canonicos},
            Equal.cong(Nat, Nat, q => 1n+q, S.quantidade_valores(segmentos), n, quantidade),
            Equal.cong(List<&2, U32>, List<&2, U32>, r => B.concatenar(bs, r), S.bytes_valores(segmentos), payload, bytes)}
    case Some{bs} P.Impossivel{}:
      Unit{}
    case Some{bs} P.Atomo{payload}:
      Unit{}
    case Some{bs} P.Registro{n, payload}:
      Unit{}

law lista_valida_expoe_segmentacao_parcial:
  for +v: D.Valor
  for +valido: {D.valor_valido(v) == True{} : Bool}
  for forma: {D.eh_lista(v) == True{} : Bool}
  ParcialLista(v, P.codificar_parcial(v))
def lista_valida_expoe_segmentacao_parcial(v, valido, forma):
  match v:
    case D.VListaVazia{}:
      ListaSegmentada{Nil{}, {==}, Unit{}, {==}, {==}}
    case D.VLista{+h, +t}:
      +cabeca_forma = F.e_booleano_esquerda(D.valor_valido(h) && D.eh_lista(t), D.valor_valido(t), valido)
      expor_cabeca_lista(h, t, P.finalizar(P.codificar_parcial(h)), P.codificar_parcial(t),
        F.e_booleano_esquerda(D.valor_valido(h), D.eh_lista(t), cabeca_forma), {==},
        lista_valida_expoe_segmentacao_parcial(t,
          F.e_booleano_direita(D.valor_valido(h) && D.eh_lista(t), D.valor_valido(t), valido),
          F.e_booleano_direita(D.valor_valido(h), D.eh_lista(t), cabeca_forma)))
    case D.VAusente{}:
      F.absurdo_booleano(ParcialLista(v, P.codificar_parcial(v)), forma)
    case D.VBool{b}:
      F.absurdo_booleano(ParcialLista(v, P.codificar_parcial(v)), forma)
    case D.VInt{a, b}:
      F.absurdo_booleano(ParcialLista(v, P.codificar_parcial(v)), forma)
    case D.VTexto{s}:
      F.absurdo_booleano(ParcialLista(v, P.codificar_parcial(v)), forma)
    case D.VRegistroVazio{}:
      F.absurdo_booleano(ParcialLista(v, P.codificar_parcial(v)), forma)
    case D.VRegistro{n, x, r}:
      F.absurdo_booleano(ParcialLista(v, P.codificar_parcial(v)), forma)

type ListaExposta<-v: D.Valor, -bs: List<&2, U32>> is Type:
  ListaExposta{segmentos: List<&2, S.ValorSegmentado>, numero: B.Numero64,
    valor: {v == A.anexar_lista(S.valores(segmentos), D.VListaVazia{}) : D.Valor},
    canonicos: S.ValoresCanonicos(segmentos),
    medida: {B.nat64(S.quantidade_valores(segmentos)) == Some{numero} : Maybe<&2, B.Numero64>},
    bytes: {bs == M.prefixo(5, numero, S.bytes_valores(segmentos)) : List<&2, U32>}}

def finalizar_lista_com_cabecalho(+v: D.Valor, +n: Nat, +payload: List<&2, U32>, +bs: List<&2, U32>,
  estrutura: ListaSegmentada<v, n, payload>, cabecalho: Cabecalho<5, n, payload, bs>) -> ListaExposta<v, bs>:
  match estrutura cabecalho:
    case ListaSegmentada{+segmentos, valor, canonicos, quantidade, bytes} Cabecalho{+numero, medida, bytes_todos}:
      ListaExposta{segmentos, numero, valor, canonicos,
        Equal.trans(Maybe<&2, B.Numero64>, B.nat64(S.quantidade_valores(segmentos)), B.nat64(n), Some{numero},
          Equal.cong(Nat, Maybe<&2, B.Numero64>, k => B.nat64(k), S.quantidade_valores(segmentos), n, quantidade), medida),
        Equal.trans(List<&2, U32>, bs, M.prefixo(5, numero, payload), M.prefixo(5, numero, S.bytes_valores(segmentos)), bytes_todos,
          Equal.cong(List<&2, U32>, List<&2, U32>, p => M.prefixo(5, numero, p), payload, S.bytes_valores(segmentos),
            Equal.sym(List<&2, U32>, S.bytes_valores(segmentos), payload, bytes)))}

def finalizar_lista_exposta(+v: D.Valor, +bs: List<&2, U32>, p: P.Parcial,
  estrutura: ParcialLista(v, p), codificado: {P.finalizar(p) == Some{bs} : Maybe<&2, List<&2, U32>>}) -> ListaExposta<v, bs>:
  match p:
    case P.Impossivel{}:
      L.ex_falso(ListaExposta<v, bs>, F.nenhum_nao_algum(List<&2, U32>, bs, codificado))
    case P.Lista{+n, +payload}:
      finalizar_lista_com_cabecalho(v, n, payload, bs, estrutura,
        campo_variavel_expoe_medida_e_bytes(5, n, payload, bs, codificado))
    case P.Atomo{payload}:
      L.ex_falso(ListaExposta<v, bs>, estrutura)
    case P.Registro{n, payload}:
      L.ex_falso(ListaExposta<v, bs>, estrutura)

law lista_codificada_expoe_segmentos_contagem_e_cabecalho:
  for +v: D.Valor
  for +bs: List<&2, U32>
  for forma: {D.eh_lista(v) == True{} : Bool}
  for codificado: P.Codificacao(v, bs)
  ListaExposta<v, bs>
def lista_codificada_expoe_segmentos_contagem_e_cabecalho(v, bs, forma, codificado):
  F.com_par(ListaExposta<v, bs>, {D.valor_valido(v) == True{} : Bool},
    {P.finalizar(P.codificar_parcial(v)) == Some{bs} : Maybe<&2, List<&2, U32>>},
    M.filho_canonico_expoe_validade_e_bytes(v, bs, codificado),
    valido => parcial => finalizar_lista_exposta(v, bs, P.codificar_parcial(v),
      lista_valida_expoe_segmentacao_parcial(v, valido, forma), parcial))
