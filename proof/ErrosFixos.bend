# Artefatos fixos do host; bytes comparados ao encoder ORIGINAL.
# Nao afirma a justificativa do status nem escolhe fatos do ambiente.
import Base
import ../contrato/Semantica.bend as S
import ../contrato/Protocolo.bend as P

type Erro is Data:
  Entrada{}
  Autenticacao{}
  Certificado{}
  Dados{}
  Limite{}
  Falha{}

def status(e: Erro) -> S.Status:
  match e:
    case Entrada{}:
      S.Entrada{}
    case Autenticacao{}:
      S.Autenticacao{}
    case Certificado{}:
      S.Certificado{}
    case Dados{}:
      S.Dados{}
    case Limite{}:
      S.Limite{}
    case Falha{}:
      S.Falha{}

def bytes(e: Erro) -> List<&2, U32>:
  match e:
    case Entrada{}:
      [0, 0, 0, 0, 0, 0, 0, 55, 6, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 6, 115, 116, 97, 116, 117, 115, 4, 0, 0, 0, 0, 0, 0, 0, 7, 101, 110, 116, 114, 97, 100, 97, 4, 0, 0, 0, 0, 0, 0, 0, 5, 118, 97, 108, 111, 114, 0]
    case Autenticacao{}:
      [0, 0, 0, 0, 0, 0, 0, 60, 6, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 6, 115, 116, 97, 116, 117, 115, 4, 0, 0, 0, 0, 0, 0, 0, 12, 97, 117, 116, 101, 110, 116, 105, 99, 97, 99, 97, 111, 4, 0, 0, 0, 0, 0, 0, 0, 5, 118, 97, 108, 111, 114, 0]
    case Certificado{}:
      [0, 0, 0, 0, 0, 0, 0, 59, 6, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 6, 115, 116, 97, 116, 117, 115, 4, 0, 0, 0, 0, 0, 0, 0, 11, 99, 101, 114, 116, 105, 102, 105, 99, 97, 100, 111, 4, 0, 0, 0, 0, 0, 0, 0, 5, 118, 97, 108, 111, 114, 0]
    case Dados{}:
      [0, 0, 0, 0, 0, 0, 0, 53, 6, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 6, 115, 116, 97, 116, 117, 115, 4, 0, 0, 0, 0, 0, 0, 0, 5, 100, 97, 100, 111, 115, 4, 0, 0, 0, 0, 0, 0, 0, 5, 118, 97, 108, 111, 114, 0]
    case Limite{}:
      [0, 0, 0, 0, 0, 0, 0, 54, 6, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 6, 115, 116, 97, 116, 117, 115, 4, 0, 0, 0, 0, 0, 0, 0, 6, 108, 105, 109, 105, 116, 101, 4, 0, 0, 0, 0, 0, 0, 0, 5, 118, 97, 108, 111, 114, 0]
    case Falha{}:
      [0, 0, 0, 0, 0, 0, 0, 53, 6, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 6, 115, 116, 97, 116, 117, 115, 4, 0, 0, 0, 0, 0, 0, 0, 5, 102, 97, 108, 104, 97, 4, 0, 0, 0, 0, 0, 0, 0, 5, 118, 97, 108, 111, 114, 0]

law todos_os_erros_preparados_sao_exatamente_mensagens_originais:
  for e: Erro
  {P.enquadrar(S.resposta_valor(S.resposta_erro(status(e)))) == Some{bytes(e)} : Maybe<&2, List<&2, U32>>}

def todos_os_erros_preparados_sao_exatamente_mensagens_originais(e):
  match e:
    case Entrada{}:
      {==}
    case Autenticacao{}:
      {==}
    case Certificado{}:
      {==}
    case Dados{}:
      {==}
    case Limite{}:
      {==}
    case Falha{}:
      {==}

