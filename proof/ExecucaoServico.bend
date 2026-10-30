# Protocolo dos passos reais de Nucleo, sem copiar continuacoes ou programas.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Protocolo.bend as P
import ../contrato/Interface.bend as I
import ../contrato/Vinculos.bend as V
import ../contrato/Logica.bend as L
import ../src/Nucleo.bend as N
import ./Fundamentos.bend as F
import ./Maquina.bend as M
import ./CodecSomasOrdem.bend as Numeros
import ./CodecRelaxarAritmeticaNat.bend as Aritmetica
import ./ProtocoloServico.bend as Q
import ./Chamada.bend as Chamada

# O resultado Data determina o prefixo, independentemente da continuacao linear.
def apos(resultado: D.ResultadoOp, s: D.Estado, o: D.Operacao,
  ts: List<&2, S.Evento>) -> S.Percurso:
  match resultado:
    case D.FalhaDados{}:
      S.Final{s, S.acrescentar(ts, S.Evento{o, S.ErroDeDados{}}), S.resposta_erro(S.Dados{})}
    case D.Observado{obs}:
      S.Prefixo{s, S.acrescentar(ts, S.Evento{o, S.Leitura{obs}})}
    case D.Alterado{w}:
      S.Prefixo{w, S.acrescentar(ts, S.Evento{o, S.Escrita{}})}

law apos_satisfaz_vinculo:
  for resultado: D.ResultadoOp
  for -s: D.Estado
  for -o: D.Operacao
  for -ts: List<&2, S.Evento>
  V.AposOperacao(resultado, s, o, ts, apos(resultado, s, o, ts))
def apos_satisfaz_vinculo(resultado, s, o, ts):
  match resultado:
    case D.FalhaDados{}: {==}
    case D.Observado{obs}: L.Ambos{{==}, {==}}
    case D.Alterado{w}: L.Ambos{{==}, {==}}

law apos_e_o_passo_real:
  for resultado: D.ResultadoOp
  for -s: D.Estado
  for -o: D.Operacao
  for -ts: List<&2, S.Evento>
  for -k: S.Retorno -> S.Acao
  {apos(resultado, s, o, ts) ==
    N.instantaneo(N.passo_maquina(S.aplicar(resultado, s, o, k), ts)) : S.Percurso}
def apos_e_o_passo_real(resultado, s, o, ts, k):
  match resultado:
    case D.FalhaDados{}: {==}
    case D.Observado{obs}: {==}
    case D.Alterado{w}: {==}

law menor_sucessor:
  for n: Nat
  {Nat.is_lt(n, Succ{n}) == True{} : Bool}
def menor_sucessor(n):
  match n:
    case 0n: {==}
    case 1n+k: menor_sucessor(k)

# Uma janela entre b e b+2 tem somente a posicao b+1.
law nao_menor_zero:
  for n: Nat
  {Nat.is_lt(n, 0n) == False{} : Bool}
def nao_menor_zero(n):
  match n:
    case 0n: {==}
    case 1n+k: {==}

law unico_entre_dois_sucessores:
  for b: Nat
  for u: Nat
  for esquerda: {Nat.is_lt(b, u) == True{} : Bool}
  for direita: {Nat.is_lt(u, Succ{Succ{b}}) == True{} : Bool}
  {u == Succ{b} : Nat}
def unico_entre_dois_sucessores(b, u, esquerda, direita):
  match b u:
    case 0n 0n:
      F.absurdo_booleano({0n == 1n : Nat}, esquerda)
    case 0n 1n+k:
      match k:
        case 0n: {==}
        case 1n+j:
          F.absurdo_booleano({Succ{Succ{j}} == 1n : Nat},
            Equal.trans(Bool, False{}, Nat.is_lt(j, 0n), True{},
              Equal.sym(Bool, Nat.is_lt(j, 0n), False{}, nao_menor_zero(j)), direita))
    case 1n+b 0n:
      F.absurdo_booleano({0n == Succ{Succ{b}} : Nat}, esquerda)
    case 1n+b 1n+u:
      Equal.cong(Nat, Nat, x => Succ{x}, u, Succ{b},
        unico_entre_dois_sucessores(b, u, esquerda, direita))

def consultar(xs: List<&2, Q.QuadroExec>, n: Nat) -> Maybe<&2, Q.QuadroExec>:
  match xs n:
    case Nil{} _: None{}
    case Con{h, t} 0n: Some{h}
    case Con{h, t} 1n+k: consultar(t, k)

type Sequencia is Data:
  Sequencia{cabeca: Q.QuadroExec, cauda: List<&2, Q.QuadroExec>}

def cabeca(s: Sequencia) -> Q.QuadroExec:
  Sequencia{h, t} = s
  h

def cauda(s: Sequencia) -> List<&2, Q.QuadroExec>:
  Sequencia{h, t} = s
  t

def expandir(+s: Sequencia) -> List<&2, Q.QuadroExec>:
  Con{cabeca(s), cauda(s)}

# n e so testemunha matematica; a sequencia para no primeiro estado Parada.
def gerar_sequencia(n: Nat, m: N.Maquina, +e: D.Esquema) -> Sequencia:
  match n m:
    case _ N.Parada{w, ts, r}:
      Sequencia{Q.Avaliacao{S.Final{w, ts, r}}, Nil{}}
    case 0n N.EmCurso{w, a, ts}:
      Sequencia{Q.Avaliacao{S.Prefixo{w, ts}}, Nil{}}
    case 1n+j N.EmCurso{+w, a, +ts}:
      match a:
        case S.Terminar{v}:
          Sequencia{Q.Avaliacao{S.Prefixo{w, ts}}, [Q.Avaliacao{S.Final{w, ts, S.Resposta{S.Sucesso{}, v}}}]}
        case S.Recusar{v}:
          Sequencia{Q.Avaliacao{S.Prefixo{w, ts}}, [Q.Avaliacao{S.Final{w, ts, S.Resposta{S.Recusa{}, v}}}]}
        case S.Acessar{+o, k}:
          +res = D.operar(e, w, o)
          Sequencia{Q.Avaliacao{S.Prefixo{w, ts}}, Q.Operacao{e, w, o, res} <>
            expandir(gerar_sequencia(j, N.passo_maquina(S.aplicar(res, w, o, k), ts), e))}

def gerar(n: Nat, m: N.Maquina, e: D.Esquema) -> List<&2, Q.QuadroExec>:
  expandir(gerar_sequencia(n, m, e))

law gerar_comeca_no_estado_real:
  for n: Nat
  for m: N.Maquina
  for -e: D.Esquema
  {consultar(gerar(n, m, e), 0n) == Some{Q.Avaliacao{N.instantaneo(m)}} : Maybe<&2, Q.QuadroExec>}
def gerar_comeca_no_estado_real(n, m, e):
  match n m:
    case _ N.Parada{w, ts, r}: {==}
    case 0n N.EmCurso{w, a, ts}: {==}
    case 1n+j N.EmCurso{w, a, ts}:
      match a:
        case S.Terminar{v}: {==}
        case S.Recusar{v}: {==}
        case S.Acessar{o, k}: {==}

def OperacaoCorreta(-xs: List<&2, Q.QuadroExec>, -t: Nat, q: Q.QuadroExec, -e: D.Esquema) -> Type:
  match q:
    case Q.Avaliacao{percurso}: Unit
    case Q.Operacao{e2, s, o, r}:
      L.E<{e2 == e : D.Esquema}, L.E<{r == D.operar(e, s, o) : D.ResultadoOp},
        &b: Nat -> &ts: List<&2, S.Evento> ->
          L.E<{t == Succ{b} : Nat},
            L.E<{consultar(xs, b) == Some{Q.Avaliacao{S.Prefixo{s, ts}}} : Maybe<&2, Q.QuadroExec>},
              {consultar(xs, Succ{Succ{b}}) == Some{Q.Avaliacao{apos(r, s, o, ts)}} : Maybe<&2, Q.QuadroExec>}>>>>

# Nao ha premissa de unicidade: os vizinhos sao consultas da sequencia produzida.
def avaliacao_correta(-xs: List<&2, Q.QuadroExec>, -t: Nat, -e: D.Esquema,
  +percurso: S.Percurso, -q: Q.QuadroExec,
  igualdade: {Some{Q.Avaliacao{percurso}} == Some{q} : Maybe<&2, Q.QuadroExec>}) ->
  OperacaoCorreta(xs, t, q, e):
  %F.algum_injetivo(Q.QuadroExec, Q.Avaliacao{percurso}, q, igualdade) : OperacaoCorreta(xs, t, _, e)
  Unit{}

def deslocar_operacao(-a: Q.QuadroExec, -b: Q.QuadroExec,
  -xs: List<&2, Q.QuadroExec>, -t: Nat, q: Q.QuadroExec, -e: D.Esquema,
  correta: OperacaoCorreta(xs, t, q, e)) ->
  OperacaoCorreta(Con{a, Con{b, xs}}, Succ{Succ{t}}, q, e):
  match q:
    case Q.Avaliacao{percurso}: Unit{}
    case Q.Operacao{e2, s, o, r}:
      match correta:
        case L.Ambos{esquema, L.Ambos{resultado, (inicio, ts, L.Ambos{posicao, L.Ambos{antes, depois}})}}:
          L.Ambos{esquema, L.Ambos{resultado, (Succ{Succ{inicio}}, ts,
            L.Ambos{Equal.cong(Nat, Nat, n => Succ{Succ{n}}, t, Succ{inicio}, posicao), L.Ambos{antes, depois}})}}

law todas_operacoes_geradas_sao_reais:
  for n: Nat
  for m: N.Maquina
  for +e: D.Esquema
  for t: Nat
  for +q: Q.QuadroExec
  for presente: {consultar(gerar(n, m, e), t) == Some{q} : Maybe<&2, Q.QuadroExec>}
  OperacaoCorreta(gerar(n, m, e), t, q, e)
def todas_operacoes_geradas_sao_reais(n, m, e, t, q, presente):
  match n m:
    case _ N.Parada{w, ts, r}:
      match t:
        case 0n: avaliacao_correta(gerar(n, N.Parada{w, ts, r}, e), 0n, e, S.Final{w, ts, r}, q, presente)
        case 1n+j:
          L.ex_falso(OperacaoCorreta(gerar(n, N.Parada{w, ts, r}, e), 1n+j, q, e), F.nenhum_nao_algum(Q.QuadroExec, q, presente))
    case 0n N.EmCurso{w, a, ts}:
      match t:
        case 0n: avaliacao_correta(gerar(0n, N.EmCurso{w, a, ts}, e), 0n, e, S.Prefixo{w, ts}, q, presente)
        case 1n+j:
          L.ex_falso(OperacaoCorreta(gerar(0n, N.EmCurso{w, a, ts}, e), 1n+j, q, e), F.nenhum_nao_algum(Q.QuadroExec, q, presente))
    case 1n+j N.EmCurso{+w, a, +ts}:
      match a:
        case S.Terminar{v}:
          match t:
            case 0n: avaliacao_correta(gerar(1n+j, N.EmCurso{w, S.Terminar{v}, ts}, e), 0n, e, S.Prefixo{w, ts}, q, presente)
            case 1n+k:
              match k:
                case 0n: avaliacao_correta(gerar(1n+j, N.EmCurso{w, S.Terminar{v}, ts}, e), 1n, e, S.Final{w, ts, S.Resposta{S.Sucesso{}, v}}, q, presente)
                case 1n+i:
                  L.ex_falso(OperacaoCorreta(gerar(1n+j, N.EmCurso{w, S.Terminar{v}, ts}, e), Succ{Succ{i}}, q, e), F.nenhum_nao_algum(Q.QuadroExec, q, presente))
        case S.Recusar{v}:
          match t:
            case 0n: avaliacao_correta(gerar(1n+j, N.EmCurso{w, S.Recusar{v}, ts}, e), 0n, e, S.Prefixo{w, ts}, q, presente)
            case 1n+k:
              match k:
                case 0n: avaliacao_correta(gerar(1n+j, N.EmCurso{w, S.Recusar{v}, ts}, e), 1n, e, S.Final{w, ts, S.Resposta{S.Recusa{}, v}}, q, presente)
                case 1n+i:
                  L.ex_falso(OperacaoCorreta(gerar(1n+j, N.EmCurso{w, S.Recusar{v}, ts}, e), Succ{Succ{i}}, q, e), F.nenhum_nao_algum(Q.QuadroExec, q, presente))
        case S.Acessar{+o, k}:
          match t:
            case 0n: avaliacao_correta(gerar(1n+j, N.EmCurso{w, S.Acessar{o, k}, ts}, e), 0n, e, S.Prefixo{w, ts}, q, presente)
            case 1n+i:
              match i:
                case 0n:
                  %F.algum_injetivo(Q.QuadroExec, Q.Operacao{e, w, o, D.operar(e, w, o)}, q, presente) :
                    OperacaoCorreta(gerar(1n+j, N.EmCurso{w, S.Acessar{o, k}, ts}, e), 1n, _, e)
                  L.Ambos{{==}, L.Ambos{{==}, (0n, ts, L.Ambos{{==}, L.Ambos{{==},
                    (%Equal.sym(S.Percurso, apos(D.operar(e, w, o), w, o, ts),
                      N.instantaneo(N.passo_maquina(S.aplicar(D.operar(e, w, o), w, o, k), ts)),
                      apos_e_o_passo_real(D.operar(e, w, o), w, o, ts, k)) :
                        {consultar(gerar(j, N.passo_maquina(S.aplicar(D.operar(e, w, o), w, o, k), ts), e), 0n) == Some{Q.Avaliacao{_}} : Maybe<&2, Q.QuadroExec>}
                      gerar_comeca_no_estado_real(j, N.passo_maquina(S.aplicar(D.operar(e, w, o), w, o, k), ts), e))}})}}
                case 1n+u:
                  deslocar_operacao(Q.Avaliacao{S.Prefixo{w, ts}}, Q.Operacao{e, w, o, D.operar(e, w, o)},
                    gerar(j, N.passo_maquina(S.aplicar(D.operar(e, w, o), w, o, k), ts), e), u, q, e,
                    todas_operacoes_geradas_sao_reais(j, N.passo_maquina(S.aplicar(D.operar(e, w, o), w, o, k), ts), e, u, q, presente))

# Numero de passos reais em uma posicao de avaliacao (terminal pode ocupar posicao impar).
def passos(t: Nat) -> Nat:
  match t:
    case 0n: 0n
    case 1n: 1n
    case 2n+j: 1n+passos(j)

def valor_avaliacao(q: Q.QuadroExec) -> Maybe<&2, S.Percurso>:
  match q:
    case Q.Avaliacao{p}: Some{p}
    case Q.Operacao{e, s, o, r}: None{}

def aval_injetiva(+a: S.Percurso, -b: S.Percurso,
  igual: {Some{Q.Avaliacao{a}} == Some{Q.Avaliacao{b}} : Maybe<&2, Q.QuadroExec>}) -> {a == b : S.Percurso}:
  F.algum_injetivo(S.Percurso, a, b,
    Equal.cong(Q.QuadroExec, Maybe<&2, S.Percurso>, valor_avaliacao,
      Q.Avaliacao{a}, Q.Avaliacao{b}, F.algum_injetivo(Q.QuadroExec, Q.Avaliacao{a}, Q.Avaliacao{b}, igual)))

def nao_e_avaliacao(e: D.Esquema, s: D.Estado, o: D.Operacao, r: D.ResultadoOp, -p: S.Percurso,
  igual: {Some{Q.Operacao{e, s, o, r}} == Some{Q.Avaliacao{p}} : Maybe<&2, Q.QuadroExec>}) -> Empty:
  F.nenhum_nao_algum(S.Percurso, p,
    Equal.cong(Q.QuadroExec, Maybe<&2, S.Percurso>, valor_avaliacao,
      Q.Operacao{e, s, o, r}, Q.Avaliacao{p}, F.algum_injetivo(Q.QuadroExec, Q.Operacao{e, s, o, r}, Q.Avaliacao{p}, igual)))

law avaliacoes_reais:
  for n: Nat
  for m: N.Maquina
  for +e: D.Esquema
  for t: Nat
  for -p: S.Percurso
  for presente: {consultar(gerar(n, m, e), t) == Some{Q.Avaliacao{p}} : Maybe<&2, Q.QuadroExec>}
  {N.percorrer(passos(t), m, e) == p : S.Percurso}
def avaliacoes_reais(n, m, e, t, p, presente):
  match n m:
    case _ N.Parada{w, ts, r}:
      match t:
        case 0n: aval_injetiva(S.Final{w, ts, r}, p, presente)
        case 1n+j:
          L.ex_falso({N.percorrer(passos(1n+j), N.Parada{w, ts, r}, e) == p : S.Percurso}, F.nenhum_nao_algum(Q.QuadroExec, Q.Avaliacao{p}, presente))
    case 0n N.EmCurso{w, a, ts}:
      match t:
        case 0n: aval_injetiva(S.Prefixo{w, ts}, p, presente)
        case 1n+j:
          L.ex_falso({N.percorrer(passos(1n+j), N.EmCurso{w, a, ts}, e) == p : S.Percurso}, F.nenhum_nao_algum(Q.QuadroExec, Q.Avaliacao{p}, presente))
    case 1n+j N.EmCurso{+w, a, +ts}:
      match a:
        case S.Terminar{v}:
          match t:
            case 0n: aval_injetiva(S.Prefixo{w, ts}, p, presente)
            case 1n+k:
              match k:
                case 0n: aval_injetiva(S.Final{w, ts, S.Resposta{S.Sucesso{}, v}}, p, presente)
                case 1n+i:
                  L.ex_falso({N.percorrer(passos(Succ{Succ{i}}), N.EmCurso{w, S.Terminar{v}, ts}, e) == p : S.Percurso}, F.nenhum_nao_algum(Q.QuadroExec, Q.Avaliacao{p}, presente))
        case S.Recusar{v}:
          match t:
            case 0n: aval_injetiva(S.Prefixo{w, ts}, p, presente)
            case 1n+k:
              match k:
                case 0n: aval_injetiva(S.Final{w, ts, S.Resposta{S.Recusa{}, v}}, p, presente)
                case 1n+i:
                  L.ex_falso({N.percorrer(passos(Succ{Succ{i}}), N.EmCurso{w, S.Recusar{v}, ts}, e) == p : S.Percurso}, F.nenhum_nao_algum(Q.QuadroExec, Q.Avaliacao{p}, presente))
        case S.Acessar{+o, k}:
          match t:
            case 0n: aval_injetiva(S.Prefixo{w, ts}, p, presente)
            case 1n+i:
              match i:
                case 0n:
                  L.ex_falso({N.percorrer(1n, N.EmCurso{w, S.Acessar{o, k}, ts}, e) == p : S.Percurso}, nao_e_avaliacao(e, w, o, D.operar(e, w, o), p, presente))
                case 1n+u:
                  avaliacoes_reais(j, N.passo_maquina(S.aplicar(D.operar(e, w, o), w, o, k), ts), e, u, p, presente)

law passos_preserva_ordem:
  for u: Nat
  for v: Nat
  for ordem: {Nat.is_lt(u, v) == True{} : Bool}
  {Nat.is_le(passos(u), passos(v)) == True{} : Bool}
def passos_preserva_ordem(u, v, ordem):
  match u v:
    case 0n _: Aritmetica.zero_nao_maior(passos(v))
    case 1n 0n: F.absurdo_booleano({Nat.is_le(1n, 0n) == True{} : Bool}, ordem)
    case 1n 1n: F.absurdo_booleano({Nat.is_le(1n, 1n) == True{} : Bool}, ordem)
    case 1n 2n+j: Aritmetica.zero_nao_maior(passos(j))
    case 2n+i 0n: F.absurdo_booleano({Nat.is_le(passos(2n+i), 0n) == True{} : Bool}, ordem)
    case 2n+i 1n: F.absurdo_booleano({Nat.is_le(passos(2n+i), 1n) == True{} : Bool}, ordem)
    case 2n+i 2n+j: passos_preserva_ordem(i, j, ordem)

# O percurso real usa os mesmos indices; a ordem nao depende de escolher tracos diferentes.
law prefixos_das_avaliacoes_em_ordem:
  for +u: Nat
  for +v: Nat
  for m: N.Maquina
  for +e: D.Esquema
  for -antes: S.Percurso
  for -depois: S.Percurso
  for ordem: {Nat.is_lt(u, v) == True{} : Bool}
  for primeira: {N.percorrer(passos(u), m, e) == antes : S.Percurso}
  for segunda: {N.percorrer(passos(v), m, e) == depois : S.Percurso}
  L.Prefixo(S.Evento, S.eventos_percurso(antes), S.eventos_percurso(depois))
def prefixos_das_avaliacoes_em_ordem(u, v, m, e, antes, depois, ordem, primeira, segunda):
  %segunda : L.Prefixo(S.Evento, S.eventos_percurso(antes), S.eventos_percurso(_))
  %primeira : L.Prefixo(S.Evento, S.eventos_percurso(_), S.eventos_percurso(N.percorrer(passos(v), m, e)))
  %Numeros.nat_decompor_limite(passos(u), passos(v), passos_preserva_ordem(u, v, ordem)) :
    L.Prefixo(S.Evento, S.eventos_percurso(N.percorrer(passos(u), m, e)),
      S.eventos_percurso(N.percorrer(_, m, e)))
  M.prefixos_da_maquina_em_ordem(passos(u), Nat.sub(passos(v), passos(u)), m, e)

def TerminaNoPrimeiro(xs: List<&2, Q.QuadroExec>) -> Type:
  match xs:
    case Nil{}: Unit
    case Con{Q.Avaliacao{S.Final{w, ts, r}}, t}: {t == Nil{} : List<&2, Q.QuadroExec>}
    case Con{Q.Avaliacao{S.Prefixo{w, ts}}, t}: TerminaNoPrimeiro(t)
    case Con{Q.Operacao{e, s, o, r}, t}: TerminaNoPrimeiro(t)

law gerador_para_no_primeiro_final:
  for n: Nat
  for m: N.Maquina
  for +e: D.Esquema
  TerminaNoPrimeiro(gerar(n, m, e))
def gerador_para_no_primeiro_final(n, m, e):
  match n m:
    case _ N.Parada{w, ts, r}: {==}
    case 0n N.EmCurso{w, a, ts}: Unit{}
    case 1n+j N.EmCurso{+w, a, +ts}:
      match a:
        case S.Terminar{v}: {==}
        case S.Recusar{v}: {==}
        case S.Acessar{+o, k}:
          gerador_para_no_primeiro_final(j, N.passo_maquina(S.aplicar(D.operar(e, w, o), w, o, k), ts), e)

def eh_final(p: S.Percurso) -> Bool:
  match p:
    case S.Prefixo{w, ts}: False{}
    case S.Final{w, ts, r}: True{}

def prefixo_nao_final(+w: D.Estado, +ts: List<&2, S.Evento>, -fw: D.Estado,
  -fts: List<&2, S.Evento>, -fr: S.Resposta,
  presente: {Some{Q.Avaliacao{S.Prefixo{w, ts}}} == Some{Q.Avaliacao{S.Final{fw, fts, fr}}} : Maybe<&2, Q.QuadroExec>}) -> Empty:
  F.falso_nao_verdadeiro(Equal.cong(S.Percurso, Bool,
    eh_final,
    S.Prefixo{w, ts}, S.Final{fw, fts, fr}, aval_injetiva(S.Prefixo{w, ts}, S.Final{fw, fts, fr}, presente)))

law final_impede_consulta_posterior:
  for xs: List<&2, Q.QuadroExec>
  for u: Nat
  for v: Nat
  for -fw: D.Estado
  for -fts: List<&2, S.Evento>
  for -fr: S.Resposta
  for -q: Q.QuadroExec
  for ordem: {Nat.is_lt(u, v) == True{} : Bool}
  for final: {consultar(xs, u) == Some{Q.Avaliacao{S.Final{fw, fts, fr}}} : Maybe<&2, Q.QuadroExec>}
  for depois: {consultar(xs, v) == Some{q} : Maybe<&2, Q.QuadroExec>}
  for termina: TerminaNoPrimeiro(xs)
  Empty
def final_impede_consulta_posterior(xs, u, v, fw, fts, fr, q, ordem, final, depois, termina):
  match xs:
    case Nil{}: F.nenhum_nao_algum(Q.QuadroExec, Q.Avaliacao{S.Final{fw, fts, fr}}, final)
    case Con{Q.Avaliacao{S.Final{w, ts, r}}, t}:
      match u:
        case 0n:
          match v:
            case 0n: F.falso_nao_verdadeiro(ordem)
            case 1n+j:
              F.nenhum_nao_algum(Q.QuadroExec, q,
                (%termina : {consultar(_, j) == Some{q} : Maybe<&2, Q.QuadroExec>} depois))
        case 1n+i:
          F.nenhum_nao_algum(Q.QuadroExec, Q.Avaliacao{S.Final{fw, fts, fr}},
            (%termina : {consultar(_, i) == Some{Q.Avaliacao{S.Final{fw, fts, fr}}} : Maybe<&2, Q.QuadroExec>} final))
    case Con{Q.Avaliacao{S.Prefixo{+w, +ts}}, t}:
      match u:
        case 0n: prefixo_nao_final(w, ts, fw, fts, fr, final)
        case 1n+i:
          match v:
            case 0n: F.falso_nao_verdadeiro(ordem)
            case 1n+j: final_impede_consulta_posterior(t, i, j, fw, fts, fr, q, ordem, final, depois, termina)
    case Con{Q.Operacao{e, s, o, r}, t}:
      match u:
        case 0n: nao_e_avaliacao(e, s, o, r, S.Final{fw, fts, fr}, final)
        case 1n+i:
          match v:
            case 0n: F.falso_nao_verdadeiro(ordem)
            case 1n+j: final_impede_consulta_posterior(t, i, j, fw, fts, fr, q, ordem, final, depois, termina)

def ultimo(xs: List<&2, Q.QuadroExec>) -> Maybe<&2, Q.QuadroExec>:
  match xs:
    case Nil{}: None{}
    case Con{h, Nil{}}: Some{h}
    case Con{h, Con{j, t}}: ultimo(Con{j, t})

law ultimo_dois_prefixos:
  for -a: Q.QuadroExec
  for -b: Q.QuadroExec
  for -seq: Sequencia
  {ultimo(Con{a, Con{b, expandir(seq)}}) == ultimo(expandir(seq)) : Maybe<&2, Q.QuadroExec>}
def ultimo_dois_prefixos(a, b, seq):
  {==}

law ultimo_representa_todo_percurso:
  for +n: Nat
  for m: N.Maquina
  for +e: D.Esquema
  {ultimo(gerar(n, m, e)) == Some{Q.Avaliacao{N.percorrer(n, m, e)}} : Maybe<&2, Q.QuadroExec>}
def ultimo_representa_todo_percurso(n, m, e):
  match n m:
    case _ N.Parada{+w, +ts, +r}:
      %Equal.sym(S.Percurso, N.percorrer(n, N.Parada{w, ts, r}, e), S.Final{w, ts, r},
        N.parada_absorve(n, w, ts, r, e)) :
          {ultimo(gerar(n, N.Parada{w, ts, r}, e)) == Some{Q.Avaliacao{_}} : Maybe<&2, Q.QuadroExec>}
      {==}
    case 0n N.EmCurso{w, a, ts}: {==}
    case 1n+j N.EmCurso{+w, a, +ts}:
      match a:
        case S.Terminar{+v}:
          %Equal.sym(S.Percurso, N.percorrer(j, N.Parada{w, ts, S.Resposta{S.Sucesso{}, v}}, e), S.Final{w, ts, S.Resposta{S.Sucesso{}, v}},
            N.parada_absorve(j, w, ts, S.Resposta{S.Sucesso{}, v}, e)) :
              {ultimo(gerar(1n+j, N.EmCurso{w, S.Terminar{v}, ts}, e)) == Some{Q.Avaliacao{_}} : Maybe<&2, Q.QuadroExec>}
          {==}
        case S.Recusar{+v}:
          %Equal.sym(S.Percurso, N.percorrer(j, N.Parada{w, ts, S.Resposta{S.Recusa{}, v}}, e), S.Final{w, ts, S.Resposta{S.Recusa{}, v}},
            N.parada_absorve(j, w, ts, S.Resposta{S.Recusa{}, v}, e)) :
              {ultimo(gerar(1n+j, N.EmCurso{w, S.Recusar{v}, ts}, e)) == Some{Q.Avaliacao{_}} : Maybe<&2, Q.QuadroExec>}
          {==}
        case S.Acessar{+o, k}:
          Equal.trans(Maybe<&2, Q.QuadroExec>,
            ultimo(gerar(1n+j, N.EmCurso{w, S.Acessar{o, k}, ts}, e)),
            ultimo(gerar(j, N.passo_maquina(S.aplicar(D.operar(e, w, o), w, o, k), ts), e)),
            Some{Q.Avaliacao{N.percorrer(j, N.passo_maquina(S.aplicar(D.operar(e, w, o), w, o, k), ts), e)}},
            ultimo_dois_prefixos(Q.Avaliacao{S.Prefixo{w, ts}}, Q.Operacao{e, w, o, D.operar(e, w, o)},
              gerar_sequencia(j, N.passo_maquina(S.aplicar(D.operar(e, w, o), w, o, k), ts), e)),
            ultimo_representa_todo_percurso(j, N.passo_maquina(S.aplicar(D.operar(e, w, o), w, o, k), ts), e))

def subir_indice(-h: Q.QuadroExec, -t: List<&2, Q.QuadroExec>, -q: Q.QuadroExec,
  resultado: &n: Nat -> {consultar(t, n) == Some{q} : Maybe<&2, Q.QuadroExec>}) ->
  &n: Nat -> {consultar(Con{h, t}, n) == Some{q} : Maybe<&2, Q.QuadroExec>}:
  match resultado:
    case (n, igual): (1n+n, igual)

law ultimo_presente_tem_indice:
  for xs: List<&2, Q.QuadroExec>
  for -q: Q.QuadroExec
  for presente: {ultimo(xs) == Some{q} : Maybe<&2, Q.QuadroExec>}
  exs n: Nat
  {consultar(xs, n) == Some{q} : Maybe<&2, Q.QuadroExec>}
def ultimo_presente_tem_indice(xs, q, presente):
  match xs:
    case Nil{}:
      L.ex_falso((&n: Nat -> {consultar(Nil{}, n) == Some{q} : Maybe<&2, Q.QuadroExec>}), F.nenhum_nao_algum(Q.QuadroExec, q, presente))
    case Con{h, Nil{}}: (0n, presente)
    case Con{h, Con{j, t}}:
      subir_indice(h, Con{j, t}, q, ultimo_presente_tem_indice(Con{j, t}, q, presente))

def expandir_quadro(r: P.Requisicao, ctx: D.Contexto, q: Q.QuadroExec) -> Q.Quadro:
  match q:
    case Q.Avaliacao{p}: Q.Avaliada{r, ctx, p}
    case Q.Operacao{e, s, o, resultado}: Q.Operada{e, s, o, resultado}

def Reflexao(-r: P.Requisicao, -ctx: D.Contexto, -local: Maybe<&2, Q.QuadroExec>, q: Q.Quadro) -> Type:
  match q:
    case Q.Avaliada{r2, ctx2, p}:
      L.E<{r2 == r : P.Requisicao}, L.E<{ctx2 == ctx : D.Contexto},
        {local == Some{Q.Avaliacao{p}} : Maybe<&2, Q.QuadroExec>}>>
    case Q.Operada{e, s, o, resultado}:
      {local == Some{Q.Operacao{e, s, o, resultado}} : Maybe<&2, Q.QuadroExec>}
    case _: Empty

law expandir_reflete_consulta:
  for +r: P.Requisicao
  for +ctx: D.Contexto
  for xs: List<&2, Q.QuadroExec>
  for t: Nat
  for -q: Q.Quadro
  for presente: {Q.consultar(Q.expandir_exec(r, ctx, xs), t) == Some{q} : Maybe<&2, Q.Quadro>}
  Reflexao(r, ctx, consultar(xs, t), q)
def expandir_reflete_consulta(r, ctx, xs, t, q, presente):
  match xs t:
    case Nil{} _:
      L.ex_falso(Reflexao(r, ctx, consultar(Nil{}, t), q), F.nenhum_nao_algum(Q.Quadro, q, presente))
    case Con{Q.Avaliacao{+p}, resto} 0n:
      %F.algum_injetivo(Q.Quadro, Q.Avaliada{r, ctx, p}, q, presente) :
        Reflexao(r, ctx, consultar(Con{Q.Avaliacao{p}, resto}, 0n), _)
      L.Ambos{{==}, L.Ambos{{==}, {==}}}
    case Con{Q.Operacao{+e, +s, +o, +resultado}, resto} 0n:
      %F.algum_injetivo(Q.Quadro, Q.Operada{e, s, o, resultado}, q, presente) :
        Reflexao(r, ctx, consultar(Con{Q.Operacao{e, s, o, resultado}, resto}, 0n), _)
      {==}
    case Con{Q.Avaliacao{p}, resto} 1n+j:
      expandir_reflete_consulta(r, ctx, resto, j, q, presente)
    case Con{Q.Operacao{e, s, o, resultado}, resto} 1n+j:
      expandir_reflete_consulta(r, ctx, resto, j, q, presente)

law expandir_preserva_consulta:
  for +r: P.Requisicao
  for +ctx: D.Contexto
  for xs: List<&2, Q.QuadroExec>
  for t: Nat
  for -q: Q.QuadroExec
  for presente: {consultar(xs, t) == Some{q} : Maybe<&2, Q.QuadroExec>}
  {Q.consultar(Q.expandir_exec(r, ctx, xs), t) == Some{expandir_quadro(r, ctx, q)} : Maybe<&2, Q.Quadro>}
def expandir_preserva_consulta(r, ctx, xs, t, q, presente):
  match xs t:
    case Nil{} _:
      L.ex_falso({Q.consultar(Q.expandir_exec(r, ctx, Nil{}), t) == Some{expandir_quadro(r, ctx, q)} : Maybe<&2, Q.Quadro>},
        F.nenhum_nao_algum(Q.QuadroExec, q, presente))
    case Con{Q.Avaliacao{+p}, resto} 0n:
      Equal.cong(Q.QuadroExec, Maybe<&2, Q.Quadro>, h => Some{expandir_quadro(r, ctx, h)},
        Q.Avaliacao{p}, q, F.algum_injetivo(Q.QuadroExec, Q.Avaliacao{p}, q, presente))
    case Con{Q.Operacao{+e, +s, +o, +resultado}, resto} 0n:
      Equal.cong(Q.QuadroExec, Maybe<&2, Q.Quadro>, h => Some{expandir_quadro(r, ctx, h)},
        Q.Operacao{e, s, o, resultado}, q, F.algum_injetivo(Q.QuadroExec, Q.Operacao{e, s, o, resultado}, q, presente))
    case Con{Q.Avaliacao{p}, resto} 1n+j:
      expandir_preserva_consulta(r, ctx, resto, j, q, presente)
    case Con{Q.Operacao{e, s, o, resultado}, resto} 1n+j:
      expandir_preserva_consulta(r, ctx, resto, j, q, presente)

# O produtor e estatico e fechado: reconstroi a mesma raiz, sem copiar um objeto Type.
law avaliacao_exata_do_programa:
  for ~programa: Nat -> S.Programa
  for +mundo: Nat
  for -c: S.Configuracao
  for +e: D.Esquema
  for +s: D.Estado
  for +r: P.Requisicao
  for +ctx: D.Contexto
  for +n: Nat
  for +t: Nat
  for -percurso: S.Percurso
  for esquema: {e == S.esquema(c) : D.Esquema}
  for presente: {consultar(gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s), e), t) == Some{Q.Avaliacao{percurso}} : Maybe<&2, Q.QuadroExec>}
  I.ExecucaoCorreta(c, s, r, ctx, programa(mundo), percurso)
def avaliacao_exata_do_programa(programa, mundo, c, e, s, r, ctx, n, t, percurso, esquema, presente):
  (passos(t),
    (%esquema : {percurso == S.executar(passos(t), programa(mundo), _, s, ctx, I.argumentos(r)) : S.Percurso}
      Equal.trans(S.Percurso, percurso,
        N.percorrer(passos(t), N.iniciar(programa(mundo), ctx, I.argumentos(r), s), e),
        S.executar(passos(t), programa(mundo), e, s, ctx, I.argumentos(r)),
        Equal.sym(S.Percurso,
          N.percorrer(passos(t), N.iniciar(programa(mundo), ctx, I.argumentos(r), s), e), percurso,
          avaliacoes_reais(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s), e, t, percurso, presente)),
        N.fidelidade_de_todos_os_prefixos(passos(t), programa(mundo), ctx, I.argumentos(r), e, s))))

# A igualdade e da familia inteira: um unico contrato de refinamento, nao oito leis.
def observacao_real(a: I.Ambiente, k: String, x: I.Cenario) -> Nat -> I.Fato -> Type:
  t => f => I.Acontece(a, k, x, t, f)

def observacao_modelo(-c: S.Configuracao, -p: S.Programa,
  +inicial: Maybe<&2, D.Estado>, +xs: List<&2, Q.Quadro>) -> Nat -> I.Fato -> Type:
  t => f => Q.observa_servico(c, p, inicial, xs, t, f)

# Mesma ligacao de Vinculos, parametrizada pela observacao para permitir um J.
def Ligacao(-ob: Nat -> I.Fato -> Type, -x: I.Cenario, -t: Nat,
  -e: D.Esquema, -s: D.Estado, -o: D.Operacao, -resultado: D.ResultadoOp) -> Type:
  &req: P.Requisicao -> &ctx: D.Contexto -> &programa: S.Programa ->
    &ts: List<&2, S.Evento> -> &antes: Nat -> &depois: Nat -> &apos: S.Percurso ->
      L.E<{e == S.esquema(I.configuracao(x)) : D.Esquema},
        L.E<V.Janela(antes, t, depois),
          L.E<ob(antes, I.Avaliou{req, ctx, programa, S.Prefixo{s, ts}}),
            L.E<ob(depois, I.Avaliou{req, ctx, programa, apos}),
              L.E<V.AposOperacao(resultado, s, o, ts, apos),
                @u: Nat -> @e2: D.Esquema -> @s2: D.Estado -> @o2: D.Operacao -> @r2: D.ResultadoOp ->
                  {Nat.is_lt(antes, u) == True{} : Bool} -> {Nat.is_lt(u, depois) == True{} : Bool} ->
                  ob(u, I.Operou{e2, s2, o2, r2}) ->
                    L.E<{u == t : Nat}, {I.Operou{e2, s2, o2, r2} == I.Operou{e, s, o, resultado} : I.Fato}>>>>>>

def unica_da_consulta(-c: S.Configuracao, -p: S.Programa,
  +xs: List<&2, Q.Quadro>, +b: Nat, +e: D.Esquema, +s: D.Estado, +o: D.Operacao,
  conhecida: {Q.consultar(xs, Succ{b}) == Some{Q.Operada{e, s, o, D.operar(e, s, o)}} : Maybe<&2, Q.Quadro>},
  +u: Nat, -e2: D.Esquema, -s2: D.Estado, -o2: D.Operacao, -r2: D.ResultadoOp,
  esquerda: {Nat.is_lt(b, u) == True{} : Bool}, direita: {Nat.is_lt(u, Succ{Succ{b}}) == True{} : Bool},
  observada: Q.observa(c, p, xs, u, I.Operou{e2, s2, o2, r2})) ->
  L.E<{u == Succ{b} : Nat}, {I.Operou{e2, s2, o2, r2} == I.Operou{e, s, o, D.operar(e, s, o)} : I.Fato}>:
  F.com_par(
    L.E<{u == Succ{b} : Nat}, {I.Operou{e2, s2, o2, r2} == I.Operou{e, s, o, D.operar(e, s, o)} : I.Fato}>,
    {u == Succ{b} : Nat}, {u == Succ{b} : Nat},
    Chamada.duplicar_igualdade(Nat, u, Succ{b}, unico_entre_dois_sucessores(b, u, esquerda, direita)),
    guardada => posicao => L.Ambos{guardada,
      Q.observacao_unica(c, p, xs, Succ{b}, I.Operou{e2, s2, o2, r2}, I.Operou{e, s, o, D.operar(e, s, o)},
        (%posicao : Q.observa(c, p, xs, _, I.Operou{e2, s2, o2, r2}) observada),
        Q.consulta_estabelece_observacao(c, p, xs, Succ{b}, Q.Operada{e, s, o, D.operar(e, s, o)},
          I.Operou{e, s, o, D.operar(e, s, o)}, conhecida, {==}))})

def vincular_consultas(~programa: Nat -> S.Programa, +mundo: Nat, -x: I.Cenario, -c: S.Configuracao,
  +inicial: Maybe<&2, D.Estado>, +xs: List<&2, Q.Quadro>, +r: P.Requisicao, +ctx: D.Contexto,
  +e: D.Esquema, +s: D.Estado, +o: D.Operacao, +ts: List<&2, S.Evento>, +b: Nat,
  esquema: {e == S.esquema(I.configuracao(x)) : D.Esquema},
  antes: {Q.consultar(xs, b) == Some{Q.Avaliada{r, ctx, S.Prefixo{s, ts}}} : Maybe<&2, Q.Quadro>},
  operacao: {Q.consultar(xs, Succ{b}) == Some{Q.Operada{e, s, o, D.operar(e, s, o)}} : Maybe<&2, Q.Quadro>},
  depois: {Q.consultar(xs, Succ{Succ{b}}) == Some{Q.Avaliada{r, ctx, apos(D.operar(e, s, o), s, o, ts)}} : Maybe<&2, Q.Quadro>}) ->
  Ligacao(observacao_modelo(c, programa(mundo), inicial, xs), x, Succ{b}, e, s, o, D.operar(e, s, o)):
  (r, ctx, programa(mundo), ts, b, Succ{Succ{b}}, apos(D.operar(e, s, o), s, o, ts),
    L.Ambos{esquema, L.Ambos{L.Ambos{menor_sucessor(b), menor_sucessor(Succ{b})},
      L.Ambos{Q.consulta_estabelece_observacao(c, programa(mundo), xs, b, Q.Avaliada{r, ctx, S.Prefixo{s, ts}},
          I.Avaliou{r, ctx, programa(mundo), S.Prefixo{s, ts}}, antes, {==}),
        L.Ambos{Q.consulta_estabelece_observacao(c, programa(mundo), xs, Succ{Succ{b}},
            Q.Avaliada{r, ctx, apos(D.operar(e, s, o), s, o, ts)}, I.Avaliou{r, ctx, programa(mundo), apos(D.operar(e, s, o), s, o, ts)}, depois, {==}),
          L.Ambos{apos_satisfaz_vinculo(D.operar(e, s, o), s, o, ts),
            u => e2 => s2 => o2 => r2 => esquerda => direita => fato =>
              unica_da_consulta(c, programa(mundo), xs, b, e, s, o, operacao, u, e2, s2, o2, r2, esquerda, direita, fato)}}}}})

law operacao_vinculada_na_observacao_real:
  for ~programa: Nat -> S.Programa
  for +mundo: Nat
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for -c: S.Configuracao
  for +inicial: Maybe<&2, D.Estado>
  for +xs: List<&2, Q.Quadro>
  for +r: P.Requisicao
  for +ctx: D.Contexto
  for +e: D.Esquema
  for +s: D.Estado
  for +o: D.Operacao
  for +ts: List<&2, S.Evento>
  for +b: Nat
  for esquema: {e == S.esquema(I.configuracao(x)) : D.Esquema}
  for antes: {Q.consultar(xs, b) == Some{Q.Avaliada{r, ctx, S.Prefixo{s, ts}}} : Maybe<&2, Q.Quadro>}
  for operacao: {Q.consultar(xs, Succ{b}) == Some{Q.Operada{e, s, o, D.operar(e, s, o)}} : Maybe<&2, Q.Quadro>}
  for depois: {Q.consultar(xs, Succ{Succ{b}}) == Some{Q.Avaliada{r, ctx, apos(D.operar(e, s, o), s, o, ts)}} : Maybe<&2, Q.Quadro>}
  for refino: {observacao_real(a, k, x) == observacao_modelo(c, programa(mundo), inicial, xs) : Nat -> I.Fato -> Type}
  V.OperacaoVinculada(a, k, x, Succ{b}, e, s, o, D.operar(e, s, o))
def operacao_vinculada_na_observacao_real(programa, mundo, a, k, x, c, inicial, xs, r, ctx, e, s, o, ts, b,
  esquema, antes, operacao, depois, refino):
  %Equal.sym((Nat -> I.Fato -> Type), observacao_real(a, k, x),
    observacao_modelo(c, programa(mundo), inicial, xs), refino) : Ligacao(_, x, Succ{b}, e, s, o, D.operar(e, s, o))
  vincular_consultas(programa, mundo, x, c, inicial, xs, r, ctx, e, s, o, ts, b, esquema, antes, operacao, depois)
