# Consumo integral e inversao dos pre-checks do parser real.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F

def aceita(r: C.Resultado) -> Bool:
  match r:
    case C.Decodificado{v}:
      True{}
    case _:
      False{}

law entrada_nao_decodificada:
  for -v: D.Valor
  for e: {C.Entrada{} == C.Decodificado{v} : C.Resultado}
  Empty
def entrada_nao_decodificada(v, e):
  F.falso_nao_verdadeiro(Equal.cong(C.Resultado, Bool, r => aceita(r), C.Entrada{}, C.Decodificado{v}, e))

law limite_nao_decodificado:
  for -v: D.Valor
  for e: {C.Limite{} == C.Decodificado{v} : C.Resultado}
  Empty
def limite_nao_decodificado(v, e):
  F.falso_nao_verdadeiro(Equal.cong(C.Resultado, Bool, r => aceita(r), C.Limite{}, C.Decodificado{v}, e))

def PercursoAceito(-bs: List<&2, U32>, -corpo: B.Numero64, -teto: B.Numero64, -v: D.Valor) -> Type:
  {C.percorrer(bs, corpo, teto, C.Tag{C.Raiz{}}) == C.Decodificado{v} : C.Resultado}

law octetos_aceitos_foram_conferidos:
  for validos: Bool
  for -bs: List<&2, U32>
  for -corpo: B.Numero64
  for -teto: B.Numero64
  for -v: D.Valor
  for aceito: {C.decodificar_octetos(validos, bs, corpo, teto) == C.Decodificado{v} : C.Resultado}
  L.E<{validos == True{} : Bool}, PercursoAceito(bs, corpo, teto, v)>
def octetos_aceitos_foram_conferidos(validos, bs, corpo, teto, v, aceito):
  match validos:
    case False{}:
      L.ex_falso(L.E<{False{} == True{} : Bool}, PercursoAceito(bs, corpo, teto, v)>, entrada_nao_decodificada(v, aceito))
    case True{}:
      L.Ambos{{==}, aceito}

law tamanho_aceito_foi_conferido:
  for cabe: Bool
  for +bs: List<&2, U32>
  for -corpo: B.Numero64
  for -teto: B.Numero64
  for -v: D.Valor
  for aceito: {C.decodificar_tamanho(cabe, bs, corpo, teto) == C.Decodificado{v} : C.Resultado}
  L.E<{cabe == True{} : Bool},
    L.E<{B.octetos_validos(bs) == True{} : Bool}, PercursoAceito(bs, corpo, teto, v)>>
def tamanho_aceito_foi_conferido(cabe, bs, corpo, teto, v, aceito):
  match cabe:
    case False{}:
      L.ex_falso(L.E<{False{} == True{} : Bool}, L.E<{B.octetos_validos(bs) == True{} : Bool}, PercursoAceito(bs, corpo, teto, v)>>, limite_nao_decodificado(v, aceito))
    case True{}:
      L.Ambos{{==}, octetos_aceitos_foram_conferidos(B.octetos_validos(bs), bs, corpo, teto, v, aceito)}

# Corpo nao e fornecido como premissa: e extraido da medicao aceita.
type EntradaConferida<-n: Maybe<&2, B.Numero64>, -bs: List<&2, U32>, -teto: B.Numero64, -v: D.Valor> is Type:
  Conferida{corpo: B.Numero64,
    medida: {n == Some{corpo} : Maybe<&2, B.Numero64>},
    cabe: {C.menor_igual64(corpo, teto) == True{} : Bool},
    octetos: {B.octetos_validos(bs) == True{} : Bool},
    percurso: PercursoAceito(bs, corpo, teto, v)}

def montar_conferida(-n: Maybe<&2, B.Numero64>, -bs: List<&2, U32>,
  -teto: B.Numero64, -v: D.Valor, +corpo: B.Numero64,
  medida: {n == Some{corpo} : Maybe<&2, B.Numero64>},
  provas: L.E<{C.menor_igual64(corpo, teto) == True{} : Bool},
    L.E<{B.octetos_validos(bs) == True{} : Bool}, PercursoAceito(bs, corpo, teto, v)>>) ->
  EntradaConferida<n, bs, teto, v>:
  match provas:
    case L.Ambos{cabe, L.Ambos{octetos, percurso}}:
      Conferida{corpo, medida, cabe, octetos, percurso}

law medida_aceita_foi_conferida:
  for n: Maybe<&2, B.Numero64>
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for -v: D.Valor
  for aceito: {C.decodificar_medida(n, bs, teto) == C.Decodificado{v} : C.Resultado}
  EntradaConferida<n, bs, teto, v>
def medida_aceita_foi_conferida(n, bs, teto, v, aceito):
  match n:
    case None{}:
      L.ex_falso(EntradaConferida<None{}, bs, teto, v>, limite_nao_decodificado(v, aceito))
    case Some{+corpo}:
      montar_conferida(Some{corpo}, bs, teto, v, corpo, {==},
        tamanho_aceito_foi_conferido(C.menor_igual64(corpo, teto), bs, corpo, teto, v, aceito))

law aceitacao_exige_corpo_representavel_octetos_e_limite:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for -v: D.Valor
  for aceito: {C.decodificar(bs, teto) == C.Decodificado{v} : C.Resultado}
  EntradaConferida<B.nat64(B.comprimento(bs)), bs, teto, v>
def aceitacao_exige_corpo_representavel_octetos_e_limite(bs, teto, v, aceito):
  medida_aceita_foi_conferida(B.nat64(B.comprimento(bs)), bs, teto, v, aceito)

# Esta maquina auxiliar devolve o estado final do MESMO percurso, incluindo
# os dois contadores. A prova abaixo liga-a a C.percorrer por inducao.
type Quadro is Data:
  Quadro{corpo: B.Numero64, teto: B.Numero64, maquina: C.Maquina}

def avancar(q: Quadro, b: U32) -> Quadro:
  Quadro{corpo, teto, m} = q
  +resto = C.diminuir64(corpo)
  +livre = C.diminuir64(teto)
  Quadro{resto, livre, C.passo(m, b, resto, livre)}

def executar(bs: List<&2, U32>, q: Quadro) -> Quadro:
  match bs:
    case Nil{}:
      q
    case Con{b, t}:
      executar(t, avancar(q, b))

def maquina(q: Quadro) -> C.Maquina:
  Quadro{corpo, teto, m} = q
  m

def finalizar_quadro(q: Quadro) -> C.Resultado:
  C.finalizar(maquina(q))

def percorrer_quadro(bs: List<&2, U32>, q: Quadro) -> C.Resultado:
  Quadro{corpo, teto, m} = q
  C.percorrer(bs, corpo, teto, m)

law percurso_e_execucao_integral:
  for +bs: List<&2, U32>
  for +q: Quadro
  {percorrer_quadro(bs, q) == finalizar_quadro(executar(bs, q)) : C.Resultado}
def percurso_e_execucao_integral(bs, q):
  match bs q:
    case Nil{} Quadro{corpo, teto, m}:
      {==}
    case Con{+b, +t} Quadro{+corpo, +teto, +m}:
      percurso_e_execucao_integral(t, avancar(Quadro{corpo, teto, m}, b))

law execucao_de_concatenacao:
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +q: Quadro
  {executar(B.concatenar(xs, ys), q) == executar(ys, executar(xs, q)) : Quadro}
def execucao_de_concatenacao(xs, ys, q):
  match xs:
    case Nil{}:
      {==}
    case Con{b, t}:
      execucao_de_concatenacao(t, ys, avancar(q, b))

def pronto_resultado(r: C.Resultado) -> C.Maquina:
  match r:
    case C.Decodificado{valor}:
      C.Pronto{valor}
    case _:
      C.Invalido{}

law finalizar_aceita_apenas_pronto:
  for +m: C.Maquina
  for -v: D.Valor
  for aceito: {C.finalizar(m) == C.Decodificado{v} : C.Resultado}
  {m == C.Pronto{v} : C.Maquina}
def finalizar_aceita_apenas_pronto(m, v, aceito):
  match m:
    case C.Tag{pilha}:
      L.ex_falso({C.Tag{pilha} == C.Pronto{v} : C.Maquina}, entrada_nao_decodificada(v, aceito))
    case C.TagNome{pilha}:
      L.ex_falso({C.TagNome{pilha} == C.Pronto{v} : C.Maquina}, entrada_nao_decodificada(v, aceito))
    case C.Palavra{f, n, a, b, pilha}:
      L.ex_falso({C.Palavra{f, n, a, b, pilha} == C.Pronto{v} : C.Maquina}, entrada_nao_decodificada(v, aceito))
    case C.Conteudo{nome, ultimo, q, u, texto, pilha}:
      L.ex_falso({C.Conteudo{nome, ultimo, q, u, texto, pilha} == C.Pronto{v} : C.Maquina}, entrada_nao_decodificada(v, aceito))
    case C.Pronto{+x}:
      Equal.cong(C.Resultado, C.Maquina, r => pronto_resultado(r), C.Decodificado{x}, C.Decodificado{v}, aceito)
    case C.Invalido{}:
      L.ex_falso({C.Invalido{} == C.Pronto{v} : C.Maquina}, entrada_nao_decodificada(v, aceito))
    case C.Acima{}:
      L.ex_falso({C.Acima{} == C.Pronto{v} : C.Maquina}, limite_nao_decodificado(v, aceito))

law percurso_aceito_termina_pronto:
  for +bs: List<&2, U32>
  for +q: Quadro
  for -v: D.Valor
  for aceito: {percorrer_quadro(bs, q) == C.Decodificado{v} : C.Resultado}
  {maquina(executar(bs, q)) == C.Pronto{v} : C.Maquina}
def percurso_aceito_termina_pronto(bs, q, v, aceito):
  finalizar_aceita_apenas_pronto(maquina(executar(bs, q)), v,
    Equal.trans(C.Resultado, finalizar_quadro(executar(bs, q)), percorrer_quadro(bs, q), C.Decodificado{v},
      Equal.sym(C.Resultado, percorrer_quadro(bs, q), finalizar_quadro(executar(bs, q)), percurso_e_execucao_integral(bs, q)), aceito))

law invalido_absorve_todo_sufixo:
  for bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  {C.percorrer(bs, corpo, teto, C.Invalido{}) == C.Entrada{} : C.Resultado}
def invalido_absorve_todo_sufixo(bs, corpo, teto):
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      invalido_absorve_todo_sufixo(t, C.diminuir64(corpo), C.diminuir64(teto))

law acima_absorve_todo_sufixo:
  for bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  {C.percorrer(bs, corpo, teto, C.Acima{}) == C.Limite{} : C.Resultado}
def acima_absorve_todo_sufixo(bs, corpo, teto):
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      acima_absorve_todo_sufixo(t, C.diminuir64(corpo), C.diminuir64(teto))

law pronto_recusa_qualquer_octeto_extra:
  for b: U32
  for bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for v: D.Valor
  {C.percorrer(Con{b, bs}, corpo, teto, C.Pronto{v}) == C.Entrada{} : C.Resultado}
def pronto_recusa_qualquer_octeto_extra(b, bs, corpo, teto, v):
  invalido_absorve_todo_sufixo(bs, C.diminuir64(corpo), C.diminuir64(teto))

law percurso_de_concatenacao:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +q: Quadro
  {percorrer_quadro(B.concatenar(xs, ys), q) == percorrer_quadro(ys, executar(xs, q)) : C.Resultado}
def percurso_de_concatenacao(xs, ys, q):
  Equal.trans(C.Resultado, percorrer_quadro(B.concatenar(xs, ys), q), finalizar_quadro(executar(B.concatenar(xs, ys), q)), percorrer_quadro(ys, executar(xs, q)),
    percurso_e_execucao_integral(B.concatenar(xs, ys), q),
    Equal.trans(C.Resultado, finalizar_quadro(executar(B.concatenar(xs, ys), q)), finalizar_quadro(executar(ys, executar(xs, q))), percorrer_quadro(ys, executar(xs, q)),
      Equal.cong(Quadro, C.Resultado, r => finalizar_quadro(r), executar(B.concatenar(xs, ys), q), executar(ys, executar(xs, q)), execucao_de_concatenacao(xs, ys, q)),
      Equal.sym(C.Resultado, percorrer_quadro(ys, executar(xs, q)), finalizar_quadro(executar(ys, executar(xs, q))), percurso_e_execucao_integral(ys, executar(xs, q)))))
