# Inversao geral do encoder de registros. Os segmentos, a ordem e a
# medida sao conclusoes da codificacao inteira, sem premissas de filhos.
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
import ./CodecMontagemExposicao.bend as X
import ./CodecMontagemNomes.bend as N

type RegistroSegmentado<-v: D.Valor, -n: Nat, -payload: List<&2, U32>, -anterior: String> is Type:
  RegistroSegmentado{segmentos: List<&2, S.CampoSegmentado>,
    valor: {v == A.anexar_registro(S.campos(segmentos), D.VRegistroVazio{}) : D.Valor},
    canonicos: S.CamposCanonicos(segmentos),
    ordenados: A.CamposOrdenados(S.campos(segmentos), anterior),
    quantidade: {S.quantidade_campos(segmentos) == n : Nat},
    bytes: {S.bytes_campos(segmentos) == payload : List<&2, U32>}}

def ParcialRegistro(v: D.Valor, p: P.Parcial, anterior: String) -> Type:
  match p:
    case P.Impossivel{}:
      Unit
    case P.Registro{n, payload}:
      RegistroSegmentado<v, n, payload, anterior>
    case _:
      Empty

law registro_depois_exige_forma_de_registro:
  for +v: D.Valor
  for anterior: String
  for depois: {D.registro_depois(v, anterior) == True{} : Bool}
  {D.eh_registro(v) == True{} : Bool}
def registro_depois_exige_forma_de_registro(v, anterior, depois):
  match v:
    case D.VRegistroVazio{}:
      {==}
    case D.VRegistro{n, x, r}:
      {==}
    case D.VAusente{}:
      F.absurdo_booleano({D.eh_registro(v) == True{} : Bool}, depois)
    case D.VBool{b}:
      F.absurdo_booleano({D.eh_registro(v) == True{} : Bool}, depois)
    case D.VInt{a, b}:
      F.absurdo_booleano({D.eh_registro(v) == True{} : Bool}, depois)
    case D.VTexto{s}:
      F.absurdo_booleano({D.eh_registro(v) == True{} : Bool}, depois)
    case D.VListaVazia{}:
      F.absurdo_booleano({D.eh_registro(v) == True{} : Bool}, depois)
    case D.VLista{h, t}:
      F.absurdo_booleano({D.eh_registro(v) == True{} : Bool}, depois)

law nome_valido_e_depois_do_vazio:
  for +nome: String
  for valido: {D.nome_valido(nome) == True{} : Bool}
  {String.is_lt("", nome) == True{} : Bool}
def nome_valido_e_depois_do_vazio(nome, valido):
  match nome:
    case SNil{}:
      F.absurdo_booleano({String.is_lt("", nome) == True{} : Bool}, valido)
    case SCon{h, t}:
      {==}

law registro_valido_e_depois_do_vazio:
  for +v: D.Valor
  for valido: {D.valor_valido(v) == True{} : Bool}
  for forma: {D.eh_registro(v) == True{} : Bool}
  {D.registro_depois(v, "") == True{} : Bool}
def registro_valido_e_depois_do_vazio(v, valido, forma):
  match v:
    case D.VRegistroVazio{}:
      {==}
    case D.VRegistro{+n, +x, +r}:
      nome_valido_e_depois_do_vazio(n,
        F.e_booleano_esquerda(D.nome_valido(n), D.valor_valido(x),
          F.e_booleano_esquerda(D.nome_valido(n) && D.valor_valido(x), D.registro_depois(r, n),
            F.e_booleano_esquerda(D.nome_valido(n) && D.valor_valido(x) && D.registro_depois(r, n), D.valor_valido(r), valido))))
    case D.VAusente{}:
      F.absurdo_booleano({D.registro_depois(v, "") == True{} : Bool}, forma)
    case D.VBool{b}:
      F.absurdo_booleano({D.registro_depois(v, "") == True{} : Bool}, forma)
    case D.VInt{a, b}:
      F.absurdo_booleano({D.registro_depois(v, "") == True{} : Bool}, forma)
    case D.VTexto{s}:
      F.absurdo_booleano({D.registro_depois(v, "") == True{} : Bool}, forma)
    case D.VListaVazia{}:
      F.absurdo_booleano({D.registro_depois(v, "") == True{} : Bool}, forma)
    case D.VLista{h, t}:
      F.absurdo_booleano({D.registro_depois(v, "") == True{} : Bool}, forma)

def expor_cabeca_registro(+nome: String, +v: D.Valor, +r: D.Valor, +anterior: String,
  nome_resultado: Maybe<&2, List<&2, U32>>, valor_resultado: Maybe<&2, List<&2, U32>>, parcial: P.Parcial,
  +nome_valido: {D.nome_valido(nome) == True{} : Bool},
  valor_valido: {D.valor_valido(v) == True{} : Bool},
  ordem: {String.is_lt(anterior, nome) == True{} : Bool},
  nome_bytes: {P.texto(nome) == nome_resultado : Maybe<&2, List<&2, U32>>},
  valor_bytes: {P.finalizar(P.codificar_parcial(v)) == valor_resultado : Maybe<&2, List<&2, U32>>},
  resto: ParcialRegistro(r, parcial, nome)) ->
  ParcialRegistro(D.VRegistro{nome, v, r}, P.registro_casos(nome_resultado, valor_resultado, parcial), anterior):
  match nome_resultado valor_resultado parcial:
    case None{} _ _:
      Unit{}
    case Some{nb} None{} _:
      Unit{}
    case Some{+nb} Some{+vb} P.Registro{+n, +payload}:
      match resto:
        case RegistroSegmentado{+segmentos, valor, canonicos, ordenados, quantidade, bytes}:
          RegistroSegmentado{Con{S.CampoSegmentado{nome, v, nb, vb}, segmentos},
            Equal.cong(D.Valor, D.Valor, t => D.VRegistro{nome, v, t},
              r, A.anexar_registro(S.campos(segmentos), D.VRegistroVazio{}), valor),
            L.Ambos{nome_valido, L.Ambos{nome_bytes, L.Ambos{
              Equal.trans(Maybe<&2, List<&2, U32>>, P.codificar(v), P.finalizar(P.codificar_parcial(v)), Some{vb},
                K.valor_valido_libera_codificacao(v, valor_valido), valor_bytes), canonicos}}},
            L.Ambos{nome_valido, L.Ambos{ordem, ordenados}},
            Equal.cong(Nat, Nat, q => 1n+q, S.quantidade_campos(segmentos), n, quantidade),
            Equal.trans(List<&2, U32>,
              B.concatenar(B.concatenar(nb, vb), S.bytes_campos(segmentos)),
              B.concatenar(nb, B.concatenar(vb, S.bytes_campos(segmentos))),
              B.concatenar(nb, B.concatenar(vb, payload)),
              K.concatenacao_associativa(nb, vb, S.bytes_campos(segmentos)),
              Equal.cong(List<&2, U32>, List<&2, U32>, t => B.concatenar(nb, B.concatenar(vb, t)),
                S.bytes_campos(segmentos), payload, bytes))}
    case Some{nb} Some{vb} P.Impossivel{}:
      Unit{}
    case Some{nb} Some{vb} P.Atomo{payload}:
      Unit{}
    case Some{nb} Some{vb} P.Lista{n, payload}:
      Unit{}

law registro_valido_expoe_segmentacao_parcial:
  for +v: D.Valor
  for +anterior: String
  for +valido: {D.valor_valido(v) == True{} : Bool}
  for forma: {D.eh_registro(v) == True{} : Bool}
  for depois: {D.registro_depois(v, anterior) == True{} : Bool}
  ParcialRegistro(v, P.codificar_parcial(v), anterior)
def registro_valido_expoe_segmentacao_parcial(v, anterior, valido, forma, depois):
  match v:
    case D.VRegistroVazio{}:
      RegistroSegmentado{Nil{}, {==}, Unit{}, Unit{}, {==}, {==}}
    case D.VRegistro{+nome, +x, +r}:
      +cabeca_ordem = F.e_booleano_esquerda(
        D.nome_valido(nome) && D.valor_valido(x) && D.registro_depois(r, nome), D.valor_valido(r), valido)
      +cabeca = F.e_booleano_esquerda(D.nome_valido(nome) && D.valor_valido(x), D.registro_depois(r, nome), cabeca_ordem)
      +ordem_resto = F.e_booleano_direita(D.nome_valido(nome) && D.valor_valido(x), D.registro_depois(r, nome), cabeca_ordem)
      expor_cabeca_registro(nome, x, r, anterior, P.texto(nome), P.finalizar(P.codificar_parcial(x)), P.codificar_parcial(r),
        F.e_booleano_esquerda(D.nome_valido(nome), D.valor_valido(x), cabeca),
        F.e_booleano_direita(D.nome_valido(nome), D.valor_valido(x), cabeca), depois, {==}, {==},
        registro_valido_expoe_segmentacao_parcial(r, nome,
          F.e_booleano_direita(D.nome_valido(nome) && D.valor_valido(x) && D.registro_depois(r, nome), D.valor_valido(r), valido),
          registro_depois_exige_forma_de_registro(r, nome, ordem_resto), ordem_resto))
    case D.VAusente{}:
      F.absurdo_booleano(ParcialRegistro(v, P.codificar_parcial(v), anterior), forma)
    case D.VBool{b}:
      F.absurdo_booleano(ParcialRegistro(v, P.codificar_parcial(v), anterior), forma)
    case D.VInt{a, b}:
      F.absurdo_booleano(ParcialRegistro(v, P.codificar_parcial(v), anterior), forma)
    case D.VTexto{s}:
      F.absurdo_booleano(ParcialRegistro(v, P.codificar_parcial(v), anterior), forma)
    case D.VListaVazia{}:
      F.absurdo_booleano(ParcialRegistro(v, P.codificar_parcial(v), anterior), forma)
    case D.VLista{h, t}:
      F.absurdo_booleano(ParcialRegistro(v, P.codificar_parcial(v), anterior), forma)

# Alem do cabecalho tag6, cada nome expoe seu proprio tag4 e tamanho UTF-8.
type RegistroExposto<-v: D.Valor, -bs: List<&2, U32>> is Type:
  RegistroExposto{segmentos: List<&2, S.CampoSegmentado>, numero: B.Numero64,
    valor: {v == A.anexar_registro(S.campos(segmentos), D.VRegistroVazio{}) : D.Valor},
    canonicos: S.CamposCanonicos(segmentos),
    ordenados: A.CamposOrdenados(S.campos(segmentos), ""),
    nomes: N.NomesExpostos(segmentos),
    medida: {B.nat64(S.quantidade_campos(segmentos)) == Some{numero} : Maybe<&2, B.Numero64>},
    bytes: {bs == M.prefixo(6, numero, S.bytes_campos(segmentos)) : List<&2, U32>}}

def finalizar_registro_com_cabecalho(+v: D.Valor, +n: Nat, +payload: List<&2, U32>, +bs: List<&2, U32>,
  estrutura: RegistroSegmentado<v, n, payload, "">, cabecalho: X.Cabecalho<6, n, payload, bs>) -> RegistroExposto<v, bs>:
  match estrutura cabecalho:
    case RegistroSegmentado{+segmentos, valor, canonicos, ordenados, quantidade, bytes} X.Cabecalho{+numero, medida, bytes_todos}:
      F.com_par(RegistroExposto<v, bs>, S.CamposCanonicos(segmentos), N.NomesExpostos(segmentos),
        N.campos_canonicos_expoem_todos_os_nomes(segmentos, canonicos),
        campos => nomes => RegistroExposto{segmentos, numero, valor, campos, ordenados, nomes,
          Equal.trans(Maybe<&2, B.Numero64>, B.nat64(S.quantidade_campos(segmentos)), B.nat64(n), Some{numero},
            Equal.cong(Nat, Maybe<&2, B.Numero64>, k => B.nat64(k), S.quantidade_campos(segmentos), n, quantidade), medida),
          Equal.trans(List<&2, U32>, bs, M.prefixo(6, numero, payload), M.prefixo(6, numero, S.bytes_campos(segmentos)), bytes_todos,
            Equal.cong(List<&2, U32>, List<&2, U32>, p => M.prefixo(6, numero, p), payload, S.bytes_campos(segmentos),
              Equal.sym(List<&2, U32>, S.bytes_campos(segmentos), payload, bytes)))})

def finalizar_registro_exposto(+v: D.Valor, +bs: List<&2, U32>, p: P.Parcial,
  estrutura: ParcialRegistro(v, p, ""), codificado: {P.finalizar(p) == Some{bs} : Maybe<&2, List<&2, U32>>}) -> RegistroExposto<v, bs>:
  match p:
    case P.Impossivel{}:
      L.ex_falso(RegistroExposto<v, bs>, F.nenhum_nao_algum(List<&2, U32>, bs, codificado))
    case P.Registro{+n, +payload}:
      finalizar_registro_com_cabecalho(v, n, payload, bs, estrutura,
        X.campo_variavel_expoe_medida_e_bytes(6, n, payload, bs, codificado))
    case P.Atomo{payload}:
      L.ex_falso(RegistroExposto<v, bs>, estrutura)
    case P.Lista{n, payload}:
      L.ex_falso(RegistroExposto<v, bs>, estrutura)

law registro_codificado_expoe_segmentos_contagem_e_cabecalho:
  for +v: D.Valor
  for +bs: List<&2, U32>
  for +forma: {D.eh_registro(v) == True{} : Bool}
  for codificado: P.Codificacao(v, bs)
  RegistroExposto<v, bs>
def registro_codificado_expoe_segmentos_contagem_e_cabecalho(v, bs, forma, codificado):
  F.com_par(RegistroExposto<v, bs>, {D.valor_valido(v) == True{} : Bool},
    {P.finalizar(P.codificar_parcial(v)) == Some{bs} : Maybe<&2, List<&2, U32>>},
    M.filho_canonico_expoe_validade_e_bytes(v, bs, codificado),
    +valido => parcial => finalizar_registro_exposto(v, bs, P.codificar_parcial(v),
      registro_valido_expoe_segmentacao_parcial(v, "", valido, forma,
        registro_valido_e_depois_do_vazio(v, valido, forma)), parcial))
