# Politica da aplicacao: cada usuario opera sua propria tabela de tarefas.
import Base
import ./Dados.bend as D
import ./Semantica.bend as S

type Ambos<-P: Data, -Q: Data> is Data:
  Ambos{esquerda: P, direita: Q}

def campos(l: D.Linha) -> List<&2, D.Campo>:
  D.Linha{k, fs} = l
  fs

def Dono(+us: List<&2, D.Linha>, +nome: String, l: D.Linha) -> Data:
  Ambos<{D.achar_campo(campos(l), "proprietario") == Some{D.VTexto{nome}} : Maybe<&2, D.Valor>},
    {D.existe_linha(D.achar_linha(us, nome)) == True{} : Bool}>

def Linhas(+us: List<&2, D.Linha>, +nome: String, ls: List<&2, D.Linha>) -> Data:
  match ls:
    case Nil{}: Unit
    case Con{l, resto}: Ambos<Dono(us, nome, l), Linhas(us, nome, resto)>

def Tabelas(+us: List<&2, D.Linha>, ts: List<&2, D.Tabela>) -> Data:
  match ts:
    case Nil{}: Unit
    case Con{D.Tabela{nome, ls}, resto}: Ambos<Linhas(us, nome, ls), Tabelas(us, resto)>

def Donos(s: D.Estado) -> Data:
  D.Estado{ts, us} = s
  Tabelas(us, ts)

def Permitida(ctx: D.Contexto, op: D.Operacao) -> Data:
  D.Contexto{+id, tipo} = ctx
  match op:
    case D.LerCelula{D.Aplicacao{nome}, k, c}: {nome == id : String}
    case D.VerExistencia{D.Aplicacao{nome}, k}: {nome == id : String}
    case D.ContarLinhas{D.Aplicacao{nome}}: {nome == id : String}
    case D.EnumerarChaves{D.Aplicacao{nome}}: {nome == id : String}
    case D.DefinirLinha{D.Aplicacao{nome}, k, fs}:
      Ambos<{nome == id : String}, {D.achar_campo(fs, "proprietario") == Some{D.VTexto{id}} : Maybe<&2, D.Valor>}>
    case D.RemoverLinha{D.Aplicacao{nome}, k}: {nome == id : String}
    case _: {False{} == True{} : Bool}

def Permitidos(+ctx: D.Contexto, ts: List<&2, S.Evento>) -> Data:
  match ts:
    case Nil{}: Unit
    case Con{S.Evento{op, ef}, resto}: Ambos<Permitida(ctx, op), Permitidos(ctx, resto)>

def Regra(h: S.Situacao) -> Data:
  match h:
    case S.Estavel{s}: Donos(s)
    case S.Executando{s, ctx, code, args, w, ts}: Ambos<Donos(w), Permitidos(ctx, ts)>
    case S.Encerrada{s, ctx, code, args, w, ts, r}: Ambos<Donos(w), Permitidos(ctx, ts)>

def config(e: D.Esquema, lim: S.Limites, ambiente: String) -> S.Configuracao:
  S.Configuracao{e, S.MaisUmaLei{Regra, S.NenhumaLei{}}, lim, ambiente}
