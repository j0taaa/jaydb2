# Medidas fisicas, enquadramento e continuidade do canal.
# As medidas e falhas precisam corresponder ao ambiente real; um valor
# declarado pelo servidor nao demonstra, sozinho, que um recurso acabou.
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

type Recurso is Data:
  Mensagem{}
  Estado{}
  Resposta{}
  Memoria{}
  Tempo{etapa: Etapa}

type Medicao is Data:
  Medicao{recurso: Recurso, quantidade: Nat}

# Tempo e medido na unidade fixa do contrato do ambiente.
# Bytes contam somente o corpo canonico, sem o cabecalho externo.
def limite_tempo(e: Etapa, l: S.Limites) -> Nat:
  match e:
    case Enquadrar{}:
      S.Limites{a, b, c, d, t, f, g, h, i} = l
      t
    case Autenticar{}:
      S.Limites{a, b, c, d, e, t, g, h, i} = l
      t
    case Verificar{}:
      S.Limites{a, b, c, d, e, f, t, h, i} = l
      t
    case Executar{}:
      S.Limites{a, b, c, d, e, f, g, t, i} = l
      t
    case Preparar{}:
      S.Limites{a, b, c, d, e, f, g, h, t} = l
      t

def limite_em(l: S.Limites, r: Recurso) -> Nat:
  match r:
    case Mensagem{}:
      R.limite_mensagem(l)
    case Estado{}:
      R.limite_estado(l)
    case Resposta{}:
      R.limite_resposta(l)
    case Memoria{}:
      R.limite_memoria(l)
    case Tempo{e}:
      limite_tempo(e, l)

def limite(c: S.Configuracao, r: Recurso) -> Nat:
  limite_em(S.limites(c), r)

# Um tamanho exatamente igual ao teto cabe; um prazo exatamente atingido
# expira. Isto fixa a fronteira, inclusive para a memoria medida em bytes.
def excedeu_tipo(r: Recurso, quantidade: Nat, teto: Nat) -> Bool:
  match r:
    case Tempo{e}:
      Nat.is_ge(quantidade, teto)
    case _:
      Nat.is_gt(quantidade, teto)

def excedeu_em(l: S.Limites, m: Medicao) -> Bool:
  Medicao{+r, n} = m
  excedeu_tipo(r, n, limite_em(l, r))

def excedeu(c: S.Configuracao, m: Medicao) -> Bool:
  excedeu_em(S.limites(c), m)

# Condicoes de uma etapa observadas pelo ambiente. A origem autentica
# das medidas e da falha e uma obrigacao do vinculo com a implementacao.
type Condicoes is Data:
  Condicoes{etapa: Etapa, memoria: Nat, tempo: Nat, falhou: Bool}

def sem_impedimento_em(+l: S.Limites, d: Condicoes) -> Bool:
  Condicoes{e, mem, t, falhou} = d
  Bool.not(falhou) &&
    Bool.not(excedeu_em(l, Medicao{Memoria{}, mem})) &&
    Bool.not(excedeu_em(l, Medicao{Tempo{e}, t}))

def sem_impedimento(c: S.Configuracao, d: Condicoes) -> Bool:
  sem_impedimento_em(S.limites(c), d)

def SemImpedimento(-c: S.Configuracao, -d: Condicoes) -> Type:
  {sem_impedimento(c, d) == True{} : Bool}

def LimiteAtingido(-c: S.Configuracao, -m: Medicao) -> Type:
  {excedeu(c, m) == True{} : Bool}

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
