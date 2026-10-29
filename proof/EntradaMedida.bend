# Quantidade real do corpo antes de interpretar comprimentos internos.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ../src/Entrada.bend as E
import ../src/Requisicao.bend as Q
import ./CodecPercurso.bend as Percurso

law corpo_admitido_preserva_resultado_do_codec:
  for +bs: List<&2, U32>
  for corpo: B.Numero64
  for +teto: B.Numero64
  for +s: D.Estado
  for medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {E.ler_mensagem(Some{teto}, bs, s) == E.mensagem(C.decodificar(bs, teto), s) : E.PreAutenticacao}
def corpo_admitido_preserva_resultado_do_codec(bs, corpo, teto, s, medido, cabe):
  %Equal.sym(Maybe<&2, B.Numero64>, B.nat64(B.comprimento(bs)), Some{corpo}, medido) :
    {E.mensagem_medida(_, bs, teto, s) == E.mensagem(C.decodificar(bs, teto), s) : E.PreAutenticacao}
  %Equal.sym(Bool, C.menor_igual64(corpo, teto), True{}, cabe) :
    {E.mensagem_cabe(_, bs, teto, s) == E.mensagem(C.decodificar(bs, teto), s) : E.PreAutenticacao}
  {==}

law corpo_real_acima_do_teto_produz_limite:
  for +bs: List<&2, U32>
  for corpo: B.Numero64
  for +teto: B.Numero64
  for +s: D.Estado
  for medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for acima: {C.menor_igual64(corpo, teto) == False{} : Bool}
  {E.ler_mensagem(Some{teto}, bs, s) == E.ErroMensagem{S.Limite{}} : E.PreAutenticacao}
def corpo_real_acima_do_teto_produz_limite(bs, corpo, teto, s, medido, acima):
  %Equal.sym(Maybe<&2, B.Numero64>, B.nat64(B.comprimento(bs)), Some{corpo}, medido) :
    {E.mensagem_medida(_, bs, teto, s) == E.ErroMensagem{S.Limite{}} : E.PreAutenticacao}
  %Equal.sym(Bool, C.menor_igual64(corpo, teto), False{}, acima) :
    {E.mensagem_cabe(_, bs, teto, s) == E.ErroMensagem{S.Limite{}} : E.PreAutenticacao}
  {==}

law corpo_real_nao_representavel_produz_limite:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for +s: D.Estado
  for medido: {B.nat64(B.comprimento(bs)) == None{} : Maybe<&2, B.Numero64>}
  {E.ler_mensagem(Some{teto}, bs, s) == E.ErroMensagem{S.Limite{}} : E.PreAutenticacao}
def corpo_real_nao_representavel_produz_limite(bs, teto, s, medido):
  %Equal.sym(Maybe<&2, B.Numero64>, B.nat64(B.comprimento(bs)), None{}, medido) :
    {E.mensagem_medida(_, bs, teto, s) == E.ErroMensagem{S.Limite{}} : E.PreAutenticacao}
  {==}

def aceita_preserva(+bs: List<&2, U32>, +teto: B.Numero64, +s: D.Estado,
  -v: D.Valor, conferida: Percurso.EntradaConferida<B.nat64(B.comprimento(bs)), bs, teto, v>) ->
  {E.ler_mensagem(Some{teto}, bs, s) == E.mensagem(C.decodificar(bs, teto), s) : E.PreAutenticacao}:
  match conferida:
    case Percurso.Conferida{corpo, medido, cabe, octetos, percurso}:
      corpo_admitido_preserva_resultado_do_codec(bs, corpo, teto, s, medido, cabe)

# Aceitacao real ja fornece a medida e admissibilidade; nao exige novas
# hipoteses nas APIs de composicao canonica existentes.
law decodificacao_aceita_preserva_mensagem:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for +s: D.Estado
  for -v: D.Valor
  for aceito: {C.decodificar(bs, teto) == C.Decodificado{v} : C.Resultado}
  {E.ler_mensagem(Some{teto}, bs, s) == E.mensagem(C.decodificar(bs, teto), s) : E.PreAutenticacao}
def decodificacao_aceita_preserva_mensagem(bs, teto, s, v, aceito):
  aceita_preserva(bs, teto, s, v,
    Percurso.aceitacao_exige_corpo_representavel_octetos_e_limite(bs, teto, v, aceito))

law limite_interno_no_corpo_admitido_e_entrada:
  for +bs: List<&2, U32>
  for corpo: B.Numero64
  for +teto: B.Numero64
  for +s: D.Estado
  for medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  for interno: {C.decodificar(bs, teto) == C.Limite{} : C.Resultado}
  {E.ler_mensagem(Some{teto}, bs, s) == E.ErroMensagem{S.Entrada{}} : E.PreAutenticacao}
def limite_interno_no_corpo_admitido_e_entrada(bs, corpo, teto, s, medido, cabe, interno):
  Equal.trans(E.PreAutenticacao, E.ler_mensagem(Some{teto}, bs, s),
    E.mensagem(C.decodificar(bs, teto), s), E.ErroMensagem{S.Entrada{}},
    corpo_admitido_preserva_resultado_do_codec(bs, corpo, teto, s, medido, cabe),
    Equal.cong(C.Resultado, E.PreAutenticacao, r => E.mensagem(r, s), C.decodificar(bs, teto), C.Limite{}, interno))

# Caracteriza a CAUSA da saida Limite sem receber essa causa como premissa.
def QuantidadeExcedida(medida: Maybe<&2, B.Numero64>, -teto: B.Numero64) -> Type:
  match medida:
    case None{}:
      Unit
    case Some{corpo}:
      {C.menor_igual64(corpo, teto) == False{} : Bool}

def SemLimite(pre: E.PreAutenticacao) -> Type:
  match pre:
    case E.ErroMensagem{S.Limite{}}:
      Empty
    case _:
      Unit

def envelope_sem_limite(q: Maybe<&2, P.Requisicao>, -s: D.Estado) -> SemLimite(E.envelope(q, s)):
  match q:
    case None{}:
      Unit{}
    case Some{r}:
      Unit{}

law mensagem_do_codec_nunca_cria_limite_de_recurso:
  for resultado: C.Resultado
  for -s: D.Estado
  SemLimite(E.mensagem(resultado, s))
def mensagem_do_codec_nunca_cria_limite_de_recurso(resultado, s):
  match resultado:
    case C.Entrada{}:
      Unit{}
    case C.Limite{}:
      Unit{}
    case C.Decodificado{v}:
      envelope_sem_limite(Q.extrair(v), s)

def causa_no_tamanho(cabe: Bool, +bs: List<&2, U32>, +teto: B.Numero64, +s: D.Estado,
  falha: {E.mensagem_cabe(cabe, bs, teto, s) == E.ErroMensagem{S.Limite{}} : E.PreAutenticacao}) ->
  {cabe == False{} : Bool}:
  match cabe:
    case False{}:
      {==}
    case True{}:
      L.ex_falso({True{} == False{} : Bool},
        (%falha : SemLimite(_)
          mensagem_do_codec_nunca_cria_limite_de_recurso(C.decodificar(bs, teto), s)))

def causa_na_medida(medida: Maybe<&2, B.Numero64>, +bs: List<&2, U32>, +teto: B.Numero64, +s: D.Estado,
  falha: {E.mensagem_medida(medida, bs, teto, s) == E.ErroMensagem{S.Limite{}} : E.PreAutenticacao}) ->
  QuantidadeExcedida(medida, teto):
  match medida:
    case None{}:
      Unit{}
    case Some{corpo}:
      causa_no_tamanho(C.menor_igual64(corpo, teto), bs, teto, s, falha)

law mensagem_limite_exige_excesso_da_quantidade_real:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for +s: D.Estado
  for falha: {E.ler_mensagem(Some{teto}, bs, s) == E.ErroMensagem{S.Limite{}} : E.PreAutenticacao}
  QuantidadeExcedida(B.nat64(B.comprimento(bs)), teto)
def mensagem_limite_exige_excesso_da_quantidade_real(bs, teto, s, falha):
  causa_na_medida(B.nat64(B.comprimento(bs)), bs, teto, s, falha)
