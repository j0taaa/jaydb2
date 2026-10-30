# O contrato do read conserva bytes e limites logicos uint64; o parser continua original.
import Base
import ./RotasServico.bend as Rota
import ./Transporte.bend as Transporte
import ./EntradaMedida.bend as M
import ../src/Estado.bend as Estado
import ../src/Transporte.bend as T
import ./Entrada.bend as Entrada
import ../contrato/Dados.bend as D
import ../contrato/Bytes.bend as B
import ../contrato/Logica.bend as L
import ../contrato/Interface.bend as I
import ../contrato/Semantica.bend as S
import ../contrato/Protocolo.bend as P
import ../contrato/Recursos.bend as X
import ../contrato/Requisitos.bend as R
import ../src/Codec.bend as C
import ../src/Entrada.bend as E
import ./Fundamentos.bend as F

# Estes sao resultados primitivos do header/copy em Rust, nao do decoder.
def CorpoCopiado(-c: S.Configuracao, -recepcao: X.Recepcao) -> Type:
  L.E<X.RecepcaoValida(recepcao), @br: List<&2, U32> ->
    {X.decidir_recepcao(c, recepcao) == X.ProcessarCorpo{br} : X.Disposicao} ->
      &corpo: B.Numero64 -> &teto: B.Numero64 ->
        L.E<{B.nat64(B.comprimento(br)) == Some{corpo} : Maybe<&2, B.Numero64>},
          L.E<{B.nat64(R.limite_mensagem(S.limites(c))) == Some{teto} : Maybe<&2, B.Numero64>},
            {C.menor_igual64(corpo, teto) == True{} : Bool}>>>

# O snapshot e a mesma codificacao privada do estado publicado.
def EstadoCopiado(-c: S.Configuracao, +s: D.Estado, +be: List<&2, U32>) -> Type:
  &ce: B.Numero64 -> &te: B.Numero64 ->
    L.E<P.Codificacao(D.estado_valor(s), be),
      L.E<{B.nat64(B.comprimento(be)) == Some{ce} : Maybe<&2, B.Numero64>},
        L.E<{B.nat64(R.limite_estado(S.limites(c))) == Some{te} : Maybe<&2, B.Numero64>},
          {C.menor_igual64(ce, te) == True{} : Bool}>>>

# Se houvesse uma requisicao canonica nesses bytes, a composicao REAL de
# transporte/estado/codec a devolveria. Um ErroMensagem portanto a exclui.
def requisicao_pronta(pre: E.PreAutenticacao) -> Maybe<&2, P.Requisicao>:
  match pre:
    case E.Pronta{s, r}: Some{r}
    case _: None{}

law erro_do_pacote_canonico_exclui_requisicao:
  for +e: D.Esquema
  for +s: D.Estado
  for +l: S.Limites
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +bs: List<&2, U32>
  for +ce: B.Numero64
  for +cr: B.Numero64
  for +te: B.Numero64
  for +tr: B.Numero64
  for +status: S.Status
  for cod_e: P.Codificacao(D.estado_valor(s), be)
  for +montagem: {T.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for +medida_e: {B.nat64(B.comprimento(be)) == Some{ce} : Maybe<&2, B.Numero64>}
  for +medida_r: {B.nat64(B.comprimento(br)) == Some{cr} : Maybe<&2, B.Numero64>}
  for +teto_e: {B.nat64(R.limite_estado(l)) == Some{te} : Maybe<&2, B.Numero64>}
  for +teto_r: {B.nat64(R.limite_mensagem(l)) == Some{tr} : Maybe<&2, B.Numero64>}
  for +cabe_e: {C.menor_igual64(ce, te) == True{} : Bool}
  for +cabe_r: {C.menor_igual64(cr, tr) == True{} : Bool}
  for +estrutura: {D.estrutura(e, s) == True{} : Bool}
  for +erro: {E.decodificar(bs, e, l) == E.ErroMensagem{status} : E.PreAutenticacao}
  @r: P.Requisicao -> P.Codificacao(P.requisicao_valor(r), br) -> Empty
def erro_do_pacote_canonico_exclui_requisicao(e, s, l, be, br, bs, ce, cr, te, tr, status,
  cod_e, montagem, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura, erro):
  +r => cod_r => F.nenhum_nao_algum(P.Requisicao, r,
    Equal.cong(E.PreAutenticacao, Maybe<&2, P.Requisicao>, requisicao_pronta, E.ErroMensagem{status}, E.Pronta{s, r},
      Equal.trans(E.PreAutenticacao, E.ErroMensagem{status}, E.decodificar(bs, e, l), E.Pronta{s, r},
        Equal.sym(E.PreAutenticacao, E.decodificar(bs, e, l), E.ErroMensagem{status}, erro),
        Entrada.bytes_canonicos_montados_produzem_pronta_exata(e, s, r, l, be, br, bs, ce, cr, te, tr,
          cod_e, cod_r, montagem, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura))))

# So o tamanho real do corpo gera Limite; abaixo do teto esse status nao surge.
def mensagem_admitida_sem_limite(+br: List<&2, U32>, +cr: B.Numero64, +tr: B.Numero64, +s: D.Estado,
  medida: {B.nat64(B.comprimento(br)) == Some{cr} : Maybe<&2, B.Numero64>},
  cabe: {C.menor_igual64(cr, tr) == True{} : Bool}) -> M.SemLimite(E.ler_mensagem(Some{tr}, br, s)):
  %Equal.sym(E.PreAutenticacao, E.ler_mensagem(Some{tr}, br, s), E.mensagem(C.decodificar(br, tr), s),
    M.corpo_admitido_preserva_resultado_do_codec(br, cr, tr, s, medida, cabe)) : M.SemLimite(_)
  M.mensagem_do_codec_nunca_cria_limite_de_recurso(C.decodificar(br, tr), s)

def estado_lido_sem_limite(q: Maybe<&2, D.Estado>, +br: List<&2, U32>, +cr: B.Numero64, +tr: B.Numero64,
  medida: {B.nat64(B.comprimento(br)) == Some{cr} : Maybe<&2, B.Numero64>},
  cabe: {C.menor_igual64(cr, tr) == True{} : Bool}) -> M.SemLimite(E.estado_lido(q, br, Some{tr})):
  match q:
    case None{}: Unit{}
    case Some{s}: mensagem_admitida_sem_limite(br, cr, tr, s, medida, cabe)

def estado_decodificado_sem_limite(q: C.Resultado, +e: D.Esquema, +br: List<&2, U32>, +cr: B.Numero64, +tr: B.Numero64,
  medida: {B.nat64(B.comprimento(br)) == Some{cr} : Maybe<&2, B.Numero64>},
  cabe: {C.menor_igual64(cr, tr) == True{} : Bool}) -> M.SemLimite(E.estado_decodificado(q, e, br, Some{tr})):
  match q:
    case C.Decodificado{v}: estado_lido_sem_limite(Estado.decodificar(v, e), br, cr, tr, medida, cabe)
    case C.Entrada{}: Unit{}
    case C.Limite{}: Unit{}

def ler_estado_sem_limite(cap: Maybe<&2, B.Numero64>, +e: D.Esquema, +be: List<&2, U32>, +br: List<&2, U32>, +cr: B.Numero64, +tr: B.Numero64,
  medida: {B.nat64(B.comprimento(br)) == Some{cr} : Maybe<&2, B.Numero64>},
  cabe: {C.menor_igual64(cr, tr) == True{} : Bool}) -> M.SemLimite(E.ler_estado(cap, e, be, br, Some{tr})):
  match cap:
    case None{}: Unit{}
    case Some{te}: estado_decodificado_sem_limite(C.decodificar(be, te), e, br, cr, tr, medida, cabe)

law pacote_montado_com_corpo_admitido_nao_gera_limite:
  for +e: D.Esquema
  for +l: S.Limites
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +bs: List<&2, U32>
  for +cr: B.Numero64
  for +tr: B.Numero64
  for separacao: {T.separar(bs) == Some{T.Partes{be, br}} : Maybe<&2, T.Partes>}
  for medida: {B.nat64(B.comprimento(br)) == Some{cr} : Maybe<&2, B.Numero64>}
  for teto: {B.nat64(R.limite_mensagem(l)) == Some{tr} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(cr, tr) == True{} : Bool}
  M.SemLimite(E.decodificar(bs, e, l))
def pacote_montado_com_corpo_admitido_nao_gera_limite(e, l, be, br, bs, cr, tr, separacao, medida, teto, cabe):
  %Equal.sym(Maybe<&2, T.Partes>, T.separar(bs), Some{T.Partes{be, br}}, separacao) : M.SemLimite(E.partes(_, e, l))
  %Equal.sym(Maybe<&2, B.Numero64>, B.nat64(R.limite_mensagem(l)), Some{tr}, teto) :
    M.SemLimite(E.ler_estado(B.nat64(R.limite_estado(l)), e, be, br, _))
  ler_estado_sem_limite(B.nat64(R.limite_estado(l)), e, be, br, cr, tr, medida, cabe)


# O erro publico preserva a causa do corpo, nao um limite fisico do parser.
def CausaEntrada(x: I.Cenario, erro: Rota.ErroEntrada) -> Type:
  match erro:
    case Rota.Entrada{}: I.EntradaInvalida(x)
    case Rota.Limite{}: I.LimiteNaEntrada(x)

def mensagem_sem_limite_classifica_entrada(-x: I.Cenario, status: S.Status,
  sem_limite: M.SemLimite(E.ErroMensagem{status}), entrada: I.EntradaInvalida(x)) ->
  CausaEntrada(x, Rota.erro_de_mensagem(status)):
  match status:
    case S.Sucesso{}: entrada
    case S.Recusa{}: entrada
    case S.Entrada{}: entrada
    case S.Autenticacao{}: entrada
    case S.Certificado{}: entrada
    case S.Dados{}: entrada
    case S.Limite{}: match sem_limite:
    case S.Falha{}: entrada

law erro_do_corpo_processado_tem_causa_original:
  for ~c: S.Configuracao
  for +mundo: Nat
  for +s: D.Estado
  for +recepcao: X.Recepcao
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +bs: List<&2, U32>
  for +ce: B.Numero64
  for +cr: B.Numero64
  for +te: B.Numero64
  for +tr: B.Numero64
  for +status: S.Status
  for cod_e: P.Codificacao(D.estado_valor(s), be)
  for +montagem: {T.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for octetos_e: {B.octetos_validos(be) == True{} : Bool}
  for octetos_r: {B.octetos_validos(br) == True{} : Bool}
  for medida_e: {B.nat64(B.comprimento(be)) == Some{ce} : Maybe<&2, B.Numero64>}
  for +medida_r: {B.nat64(B.comprimento(br)) == Some{cr} : Maybe<&2, B.Numero64>}
  for teto_e: {B.nat64(R.limite_estado(S.limites(c))) == Some{te} : Maybe<&2, B.Numero64>}
  for +teto_r: {B.nat64(R.limite_mensagem(S.limites(c))) == Some{tr} : Maybe<&2, B.Numero64>}
  for cabe_e: {C.menor_igual64(ce, te) == True{} : Bool}
  for +cabe_r: {C.menor_igual64(cr, tr) == True{} : Bool}
  for estrutura: {D.estrutura(S.esquema(c), s) == True{} : Bool}
  for recebido: {X.decidir_recepcao(c, recepcao) == X.ProcessarCorpo{br} : X.Disposicao}
  for +erro: {E.decodificar(bs, S.esquema(c), S.limites(c)) == E.ErroMensagem{status} : E.PreAutenticacao}
  CausaEntrada(I.Atender{mundo, c, s, recepcao}, Rota.erro_de_mensagem(status))
def erro_do_corpo_processado_tem_causa_original(c, mundo, s, recepcao, be, br, bs, ce, cr, te, tr, status,
  cod_e, montagem, octetos_e, octetos_r, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura, recebido, erro):
  mensagem_sem_limite_classifica_entrada(I.Atender{mundo, c, s, recepcao}, status,
    (%erro : M.SemLimite(_)
      pacote_montado_com_corpo_admitido_nao_gera_limite(S.esquema(c), S.limites(c), be, br, bs, cr, tr,
        Transporte.separar_inverte_toda_montagem_valida(be, br, bs, montagem, octetos_e, octetos_r), medida_r, teto_r, cabe_r)),
    L.Direita{(br, L.Ambos{recebido,
      erro_do_pacote_canonico_exclui_requisicao(S.esquema(c), s, S.limites(c), be, br, bs, ce, cr, te, tr, status,
        cod_e, montagem, medida_e, medida_r, teto_e, teto_r, cabe_e, cabe_r, estrutura, erro)})})
