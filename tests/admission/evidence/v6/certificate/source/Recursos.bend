# Enquadramento, limites logicos e continuidade do canal.
# Etapas identificam falhas reais; nao fixam orcamentos de execucao.
import Base
import ./Semantica.bend as S
import ./Requisitos.bend as R
import ./Protocolo.bend as P
import ./Bytes.bend as B

type Etapa is Data:
  Enquadrar{}
  Autenticar{}
  Verificar{}
  Executar{}
  Preparar{}

# Compara um uint64 declarado com Nat sem construir 2^64 em Peano.
# Se Nat nao cabe em uint64, nenhuma declaracao uint64 e maior que ele.
def declarado_maior_casos(+alto: U32, baixo: U32, teto: Maybe<&2, B.Numero64>) -> Bool:
  match teto:
    case None{}:
      False{}
    case Some{B.Numero64{+ta, tb}}:
      U32.is_gt(alto, ta) || (U32.is_eq(alto, ta) && U32.is_gt(baixo, tb))

def declarado_maior(+alto: U32, baixo: U32, teto: Nat) -> Bool:
  declarado_maior_casos(alto, baixo, B.nat64(teto))

def declarado_igual_casos(alto: U32, baixo: U32, n: Maybe<&2, B.Numero64>) -> Bool:
  match n:
    case None{}:
      False{}
    case Some{B.Numero64{a, b}}:
      U32.is_eq(alto, a) && U32.is_eq(baixo, b)

def declarado_igual(alto: U32, baixo: U32, n: Nat) -> Bool:
  declarado_igual_casos(alto, baixo, B.nat64(n))

# Recepcao descreve bytes efetivamente recebidos, antes da decodificacao
# do valor. O ambiente precisa demonstrar RecepcaoValida para este relato.
type Recepcao is Data:
  EOFEntreMensagens{}
  # Sinal do operador entre chamadas; nao pode ser forjado em bytes cliente.
  ParadaOperador{}
  HeaderTruncado{bytes: List<&2, U32>}
  BodyTruncado{alto: U32, baixo: U32, corpo: List<&2, U32>}
  CorpoRecebido{alto: U32, baixo: U32, corpo: List<&2, U32>}

def recepcao_valida(r: Recepcao) -> Bool:
  match r:
    case EOFEntreMensagens{}:
      True{}
    case ParadaOperador{}:
      True{}
    case HeaderTruncado{+bs}:
      B.octetos_validos(bs) && Nat.is_gt(B.comprimento(bs), 0n) && Nat.is_lt(B.comprimento(bs), 8n)
    case BodyTruncado{a, b, +bs}:
      B.octetos_validos(bs) && declarado_maior(a, b, B.comprimento(bs))
    case CorpoRecebido{a, b, +bs}:
      B.octetos_validos(bs) && declarado_igual(a, b, B.comprimento(bs))

def RecepcaoValida(-r: Recepcao) -> Type:
  {recepcao_valida(r) == True{} : Bool}

type Disposicao is Data:
  EncerrarSemResposta{}
  ProcessarCorpo{corpo: List<&2, U32>}
  RecusarContinuar{status: S.Status}
  RecusarEncerrar{status: S.Status}

def truncado_casos(acima: Bool) -> Disposicao:
  match acima:
    case True{}:
      RecusarEncerrar{S.Limite{}}
    case False{}:
      RecusarEncerrar{S.Entrada{}}

def completo_casos(acima: Bool, corpo: List<&2, U32>) -> Disposicao:
  match acima:
    case True{}:
      RecusarEncerrar{S.Limite{}}
    case False{}:
      ProcessarCorpo{corpo}

def decidir_recepcao_em(l: S.Limites, r: Recepcao) -> Disposicao:
  match r:
    case EOFEntreMensagens{}:
      EncerrarSemResposta{}
    case ParadaOperador{}:
      EncerrarSemResposta{}
    case HeaderTruncado{bs}:
      RecusarEncerrar{S.Entrada{}}
    case BodyTruncado{a, b, bs}:
      truncado_casos(declarado_maior(a, b, R.limite_mensagem(l)))
    case CorpoRecebido{a, b, bs}:
      completo_casos(declarado_maior(a, b, R.limite_mensagem(l)), bs)

def decidir_recepcao(c: S.Configuracao, r: Recepcao) -> Disposicao:
  decidir_recepcao_em(S.limites(c), r)

# Um corpo completo malformado nao perde o enquadramento da proxima
# mensagem. Este resultado so vale depois de ProcessarCorpo.
def corpo_invalido() -> Disposicao:
  RecusarContinuar{S.Entrada{}}

# A entrega pode falhar depois de publicar. O estado publicado nao muda
# durante a entrega; nenhum novo status de rollback e produzido.
type Entrega is Data:
  Entregue{}
  EntregaInterrompida{}

def canal_depois_entrega(e: Entrega) -> Bool:
  match e:
    case Entregue{}:
      True{}
    case EntregaInterrompida{}:
      False{}

law eof_entre_mensagens_encerra:
  for l: S.Limites
  {decidir_recepcao_em(l, EOFEntreMensagens{}) == EncerrarSemResposta{} : Disposicao}

def eof_entre_mensagens_encerra(l):
  {==}

law cabecalho_truncado_encerra:
  for l: S.Limites
  for bs: List<&2, U32>
  {decidir_recepcao_em(l, HeaderTruncado{bs}) == RecusarEncerrar{S.Entrada{}} : Disposicao}

def cabecalho_truncado_encerra(l, bs):
  {==}

law corpo_malformado_completo_preserva_canal:
  {corpo_invalido() == RecusarContinuar{S.Entrada{}} : Disposicao}

def corpo_malformado_completo_preserva_canal():
  {==}
