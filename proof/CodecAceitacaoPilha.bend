# A raiz de um filho pode ser ligada a qualquer pilha externa. Os guards
# continuam consultando a pilha REAL, inclusive seus irmaos pendentes.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F

def ligar_pilha(p: C.Pilha, +fora: C.Pilha) -> C.Pilha:
  match p:
    case C.Raiz{}:
      fora
    case C.Lista{u, q, xs, pai}:
      C.Lista{u, q, xs, ligar_pilha(pai, fora)}
    case C.Nome{u, q, n, xs, pai}:
      C.Nome{u, q, n, xs, ligar_pilha(pai, fora)}
    case C.Campo{u, q, n, xs, pai}:
      C.Campo{u, q, n, xs, ligar_pilha(pai, fora)}

def ligar(m: C.Maquina, +fora: C.Pilha) -> C.Maquina:
  match m:
    case C.Tag{p}:
      C.Tag{ligar_pilha(p, fora)}
    case C.TagNome{p}:
      C.TagNome{ligar_pilha(p, fora)}
    case C.Palavra{f, n, a, b, p}:
      C.Palavra{f, n, a, b, ligar_pilha(p, fora)}
    case C.Conteudo{nome, u, q, cp, s, p}:
      C.Conteudo{nome, u, q, cp, s, ligar_pilha(p, fora)}
    case C.Pronto{v}:
      C.emitir(fora, v)
    case C.Invalido{}:
      C.Invalido{}
    case C.Acima{}:
      C.Acima{}

# Somente um nome no nivel raiz precisaria de um segundo tipo de retorno.
# A leitura de UM VALOR nunca alcanca esse estado; os nomes de registros
# sempre possuem o frame Nome criado pela propria abertura do registro.
def NaoRaiz(p: C.Pilha) -> Type:
  match p:
    case C.Raiz{}:
      Empty
    case _:
      Unit

def FinalidadeInterna(f: C.Finalidade, p: C.Pilha) -> Type:
  match f:
    case C.NomeTexto{}:
      NaoRaiz(p)
    case _:
      Unit

def TextoInterno(nome: Bool, p: C.Pilha) -> Type:
  match nome:
    case True{}:
      NaoRaiz(p)
    case False{}:
      Unit

def Interna(m: C.Maquina) -> Type:
  match m:
    case C.TagNome{p}:
      NaoRaiz(p)
    case C.Palavra{f, n, a, b, p}:
      FinalidadeInterna(f, p)
    case C.Conteudo{nome, u, q, cp, s, p}:
      TextoInterno(nome, p)
    case _:
      Unit

def Continua(m: C.Maquina) -> Type:
  match m:
    case C.Pronto{v}:
      Empty
    case _:
      Unit

def duplicar_nao_raiz(+p: C.Pilha, h: NaoRaiz(p)) -> L.E<NaoRaiz(p), NaoRaiz(p)>:
  match p:
    case C.Raiz{}:
      L.ex_falso(L.E<Empty, Empty>, h)
    case C.Lista{u, q, xs, pai}:
      L.Ambos{Unit{}, Unit{}}
    case C.Nome{u, q, n, xs, pai}:
      L.Ambos{Unit{}, Unit{}}
    case C.Campo{u, q, n, xs, pai}:
      L.Ambos{Unit{}, Unit{}}

def duplicar_finalidade(f: C.Finalidade, +p: C.Pilha, h: FinalidadeInterna(f, p)) ->
  L.E<FinalidadeInterna(f, p), FinalidadeInterna(f, p)>:
  match f:
    case C.NomeTexto{}:
      duplicar_nao_raiz(p, h)
    case C.Inteiro{}:
      L.Ambos{Unit{}, Unit{}}
    case C.Texto{}:
      L.Ambos{Unit{}, Unit{}}
    case C.ContaLista{}:
      L.Ambos{Unit{}, Unit{}}
    case C.ContaRegistro{}:
      L.Ambos{Unit{}, Unit{}}

def duplicar_texto(nome: Bool, +p: C.Pilha, h: TextoInterno(nome, p)) -> L.E<TextoInterno(nome, p), TextoInterno(nome, p)>:
  match nome:
    case True{}:
      duplicar_nao_raiz(p, h)
    case False{}:
      L.Ambos{Unit{}, Unit{}}

def duplicar_interna(+m: C.Maquina, h: Interna(m)) -> L.E<Interna(m), Interna(m)>:
  match m:
    case C.Tag{p}:
      L.Ambos{Unit{}, Unit{}}
    case C.TagNome{+p}:
      duplicar_nao_raiz(p, h)
    case C.Palavra{+f, n, a, b, +p}:
      duplicar_finalidade(f, p, h)
    case C.Conteudo{+nome, u, q, cp, s, +p}:
      duplicar_texto(nome, p, h)
    case C.Pronto{v}:
      L.Ambos{Unit{}, Unit{}}
    case C.Invalido{}:
      L.Ambos{Unit{}, Unit{}}
    case C.Acima{}:
      L.Ambos{Unit{}, Unit{}}

law emitir_comuta_com_a_pilha_externa:
  for +p: C.Pilha
  for +fora: C.Pilha
  for +v: D.Valor
  {ligar(C.emitir(p, v), fora) == C.emitir(ligar_pilha(p, fora), v) : C.Maquina}
def emitir_comuta_com_a_pilha_externa(p, fora, v):
  match p:
    case C.Raiz{}:
      {==}
    case C.Lista{True{}, q, xs, +pai}:
      emitir_comuta_com_a_pilha_externa(pai, fora, C.montar_lista(Con{v, xs}, D.VListaVazia{}))
    case C.Lista{False{}, q, xs, pai}:
      {==}
    case C.Campo{True{}, q, n, xs, +pai}:
      emitir_comuta_com_a_pilha_externa(pai, fora, C.montar_registro(Con{D.Campo{n, v}, xs}, D.VRegistroVazio{}))
    case C.Campo{False{}, q, n, xs, pai}:
      {==}
    case C.Nome{u, q, n, xs, pai}:
      {==}

def emitir_interno(p: C.Pilha, v: D.Valor) -> Interna(C.emitir(p, v)):
  match p:
    case C.Raiz{}:
      Unit{}
    case C.Lista{True{}, q, xs, pai}:
      emitir_interno(pai, C.montar_lista(Con{v, xs}, D.VListaVazia{}))
    case C.Lista{False{}, q, xs, pai}:
      Unit{}
    case C.Campo{True{}, q, n, xs, pai}:
      emitir_interno(pai, C.montar_registro(Con{D.Campo{n, v}, xs}, D.VRegistroVazio{}))
    case C.Campo{False{}, q, n, xs, pai}:
      Unit{}
    case C.Nome{u, q, n, xs, pai}:
      Unit{}

def nome_conferido_ligado(ok: Bool, +u: Bool, +q: B.Numero64,
  +n: String, +xs: List<&2, D.Campo>, +p: C.Pilha, +fora: C.Pilha) ->
  {ligar(C.nome_conferido(ok, u, q, n, xs, p), fora) ==
    C.nome_conferido(ok, u, q, n, xs, ligar_pilha(p, fora)) : C.Maquina}:
  match ok:
    case False{}:
      {==}
    case True{}:
      {==}

def emitir_nome_ligado(+p: C.Pilha, +n: String, +fora: C.Pilha,
  interna: NaoRaiz(p)) ->
  {ligar(C.emitir_nome(p, n), fora) == C.emitir_nome(ligar_pilha(p, fora), n) : C.Maquina}:
  match p:
    case C.Raiz{}:
      L.ex_falso({C.Invalido{} == C.emitir_nome(fora, n) : C.Maquina}, interna)
    case C.Nome{+u, +q, +anterior, +xs, +pai}:
      nome_conferido_ligado(D.nome_valido(n) && String.is_lt(anterior, n), u, q, n, xs, pai, fora)
    case C.Lista{u, q, xs, pai}:
      {==}
    case C.Campo{u, q, k, xs, pai}:
      {==}

def nome_conferido_interno(ok: Bool, u: Bool, q: B.Numero64,
  n: String, xs: List<&2, D.Campo>, p: C.Pilha) -> Interna(C.nome_conferido(ok, u, q, n, xs, p)):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      Unit{}

def emitir_nome_interno(p: C.Pilha, +n: String) -> Interna(C.emitir_nome(p, n)):
  match p:
    case C.Nome{u, q, +anterior, xs, pai}:
      nome_conferido_interno(D.nome_valido(n) && String.is_lt(anterior, n), u, q, n, xs, pai)
    case C.Raiz{}:
      Unit{}
    case C.Lista{u, q, xs, pai}:
      Unit{}
    case C.Campo{u, q, k, xs, pai}:
      Unit{}

def emitir_texto_ligado(nome: Bool, +s: String, +p: C.Pilha, +fora: C.Pilha,
  interna: TextoInterno(nome, p)) ->
  {ligar(C.emitir_texto(nome, s, p), fora) == C.emitir_texto(nome, s, ligar_pilha(p, fora)) : C.Maquina}:
  match nome:
    case False{}:
      emitir_comuta_com_a_pilha_externa(p, fora, D.VTexto{s})
    case True{}:
      emitir_nome_ligado(p, s, fora, interna)

def emitir_texto_interno(nome: Bool, s: String, p: C.Pilha) -> Interna(C.emitir_texto(nome, s, p)):
  match nome:
    case False{}:
      emitir_interno(p, D.VTexto{s})
    case True{}:
      emitir_nome_interno(p, s)

def guardar_caractere_ligado(ultimo: Bool, +nome: Bool, +q: B.Numero64,
  +s: String, +p: C.Pilha, +fora: C.Pilha, interna: TextoInterno(nome, p)) ->
  {ligar(C.guardar_caractere(ultimo, nome, q, s, p), fora) ==
    C.guardar_caractere(ultimo, nome, q, s, ligar_pilha(p, fora)) : C.Maquina}:
  match ultimo:
    case True{}:
      emitir_texto_ligado(nome, String.reverse(s), p, fora, interna)
    case False{}:
      {==}

def guardar_parcial_ligado(ultimo: Bool, +nome: Bool, +q: B.Numero64,
  +u: C.Unicode, +s: String, +p: C.Pilha, +fora: C.Pilha) ->
  {ligar(C.guardar_parcial(ultimo, nome, q, u, s, p), fora) ==
    C.guardar_parcial(ultimo, nome, q, u, s, ligar_pilha(p, fora)) : C.Maquina}:
  match ultimo:
    case True{}:
      {==}
    case False{}:
      {==}

def guardar_escalar_ligado(e: C.Escalar, +ultimo: Bool, +nome: Bool, +q: B.Numero64,
  +s: String, +p: C.Pilha, +fora: C.Pilha, interna: TextoInterno(nome, p)) ->
  {ligar(C.guardar_escalar(e, ultimo, nome, q, s, p), fora) ==
    C.guardar_escalar(e, ultimo, nome, q, s, ligar_pilha(p, fora)) : C.Maquina}:
  match e:
    case C.UTFInvalido{}:
      {==}
    case C.Caractere{cp}:
      guardar_caractere_ligado(ultimo, nome, q, SCon{Chr{cp}, s}, p, fora, interna)
    case C.Parcial{u}:
      guardar_parcial_ligado(ultimo, nome, q, u, s, p, fora)

def guardar_caractere_interno(ultimo: Bool, +nome: Bool, q: B.Numero64,
  s: String, +p: C.Pilha, interna: TextoInterno(nome, p)) -> Interna(C.guardar_caractere(ultimo, nome, q, s, p)):
  match ultimo:
    case True{}:
      emitir_texto_interno(nome, String.reverse(s), p)
    case False{}:
      interna

def guardar_parcial_interno(ultimo: Bool, +nome: Bool, q: B.Numero64,
  u: C.Unicode, s: String, +p: C.Pilha, interna: TextoInterno(nome, p)) -> Interna(C.guardar_parcial(ultimo, nome, q, u, s, p)):
  match ultimo:
    case True{}:
      Unit{}
    case False{}:
      interna

def guardar_escalar_interno(e: C.Escalar, ultimo: Bool, +nome: Bool, q: B.Numero64,
  s: String, +p: C.Pilha, interna: TextoInterno(nome, p)) -> Interna(C.guardar_escalar(e, ultimo, nome, q, s, p)):
  match e:
    case C.UTFInvalido{}:
      Unit{}
    case C.Caractere{cp}:
      guardar_caractere_interno(ultimo, nome, q, SCon{Chr{cp}, s}, p, interna)
    case C.Parcial{u}:
      guardar_parcial_interno(ultimo, nome, q, u, s, p, interna)

def abrir_nome_ligado(ok: Bool, +q: B.Numero64, +p: C.Pilha, +fora: C.Pilha) ->
  {ligar(C.abrir_nome(ok, q, p), fora) == C.abrir_nome(ok, q, ligar_pilha(p, fora)) : C.Maquina}:
  match ok:
    case False{}:
      {==}
    case True{}:
      {==}

def abrir_variavel_ligada(vazio: Bool, f: C.Finalidade, +q: B.Numero64, +p: C.Pilha, +fora: C.Pilha) ->
  {ligar(C.abrir_variavel(vazio, f, q, p), fora) == C.abrir_variavel(vazio, f, q, ligar_pilha(p, fora)) : C.Maquina}:
  match vazio f:
    case True{} C.Texto{}:
      emitir_comuta_com_a_pilha_externa(p, fora, D.VTexto{""})
    case True{} C.ContaLista{}:
      emitir_comuta_com_a_pilha_externa(p, fora, D.VListaVazia{})
    case True{} C.ContaRegistro{}:
      emitir_comuta_com_a_pilha_externa(p, fora, D.VRegistroVazio{})
    case False{} C.NomeTexto{}:
      abrir_nome_ligado(C.menor_igual64(q, B.Numero64{0, 64}), q, p, fora)
    case False{} C.Texto{}:
      {==}
    case False{} C.ContaLista{}:
      {==}
    case False{} C.ContaRegistro{}:
      {==}
    case True{} C.NomeTexto{}:
      {==}
    case _ C.Inteiro{}:
      {==}

def abrir_nome_interno(ok: Bool, q: B.Numero64, +p: C.Pilha,
  interna: NaoRaiz(p)) -> Interna(C.abrir_nome(ok, q, p)):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      interna

def abrir_variavel_interna(vazio: Bool, +f: C.Finalidade, +q: B.Numero64, +p: C.Pilha,
  interna: FinalidadeInterna(f, p)) -> Interna(C.abrir_variavel(vazio, f, q, p)):
  match vazio f:
    case True{} C.Texto{}:
      emitir_interno(p, D.VTexto{""})
    case True{} C.ContaLista{}:
      emitir_interno(p, D.VListaVazia{})
    case True{} C.ContaRegistro{}:
      emitir_interno(p, D.VRegistroVazio{})
    case False{} C.Texto{}:
      Unit{}
    case False{} C.NomeTexto{}:
      abrir_nome_interno(C.menor_igual64(q, B.Numero64{0, 64}), q, p, interna)
    case False{} C.ContaLista{}:
      Unit{}
    case False{} C.ContaRegistro{}:
      Unit{}
    case True{} C.NomeTexto{}:
      Unit{}
    case _ C.Inteiro{}:
      Unit{}

def abrir_conferido_ligado(c: C.Conferencia, +f: C.Finalidade, +q: B.Numero64, +p: C.Pilha, +fora: C.Pilha) ->
  {ligar(C.abrir_conferido(c, f, q, p), fora) == C.abrir_conferido(c, f, q, ligar_pilha(p, fora)) : C.Maquina}:
  match c:
    case C.Cabe{}:
      abrir_variavel_ligada(C.zero64(q), f, q, p, fora)
    case C.Curto{}:
      {==}
    case C.Grande{}:
      {==}

def abrir_conferido_interno(c: C.Conferencia, +f: C.Finalidade, +q: B.Numero64, +p: C.Pilha,
  interna: FinalidadeInterna(f, p)) -> Interna(C.abrir_conferido(c, f, q, p)):
  match c:
    case C.Cabe{}:
      abrir_variavel_interna(C.zero64(q), f, q, p, interna)
    case C.Curto{}:
      Unit{}
    case C.Grande{}:
      Unit{}

# Esta e a unica diferenca da maquina local: o guard ve a pilha ligada.
# Nenhum guard e removido, e os contadores reais nao sao substituidos.
def concluir_local(f: C.Finalidade, +a: U32, +b: U32, +p: C.Pilha, fora: C.Pilha,
  corpo: B.Numero64, teto: B.Numero64) -> C.Maquina:
  match f:
    case C.Inteiro{}:
      C.emitir(p, D.VInt{a, b})
    case +outra:
      +q = {B.Numero64{a, b} : B.Numero64}
      C.abrir_conferido(C.conferir(C.somar_opcionais(C.minimo_campo(outra, q), C.minimo_pilha(ligar_pilha(p, fora))), corpo, teto), outra, q, p)

def ler_local(n: Nat, +f: C.Finalidade, +a: U32, +b: U32, +x: U32,
  +p: C.Pilha, fora: C.Pilha, corpo: B.Numero64, teto: B.Numero64) -> C.Maquina:
  match n:
    case 0n:
      concluir_local(f, (a * 256 + U32.shrn(b, 24n) : U32), (b * 256 + x : U32), p, fora, corpo, teto)
    case 1n+k:
      C.Palavra{f, k, (a * 256 + U32.shrn(b, 24n) : U32), (b * 256 + x : U32), p}

def passo_local(m: C.Maquina, +fora: C.Pilha, b: U32, corpo: B.Numero64, teto: B.Numero64) -> C.Maquina:
  match m:
    case C.Palavra{f, n, a, c, p}:
      ler_local(n, f, a, c, b, p, fora, corpo, teto)
    case +outra:
      C.passo(outra, b, corpo, teto)

def concluir_local_ligado(+f: C.Finalidade, +a: U32, +b: U32, +p: C.Pilha, +fora: C.Pilha,
  +corpo: B.Numero64, +teto: B.Numero64) ->
  {ligar(concluir_local(f, a, b, p, fora, corpo, teto), fora) == C.concluir_palavra(f, a, b, ligar_pilha(p, fora), corpo, teto) : C.Maquina}:
  match f:
    case C.Inteiro{}:
      emitir_comuta_com_a_pilha_externa(p, fora, D.VInt{a, b})
    case C.Texto{}:
      +q = {B.Numero64{a, b} : B.Numero64}
      abrir_conferido_ligado(C.conferir(C.somar_opcionais(C.minimo_campo(C.Texto{}, q), C.minimo_pilha(ligar_pilha(p, fora))), corpo, teto), C.Texto{}, q, p, fora)
    case C.NomeTexto{}:
      +q = {B.Numero64{a, b} : B.Numero64}
      abrir_conferido_ligado(C.conferir(C.somar_opcionais(C.minimo_campo(C.NomeTexto{}, q), C.minimo_pilha(ligar_pilha(p, fora))), corpo, teto), C.NomeTexto{}, q, p, fora)
    case C.ContaLista{}:
      +q = {B.Numero64{a, b} : B.Numero64}
      abrir_conferido_ligado(C.conferir(C.somar_opcionais(C.minimo_campo(C.ContaLista{}, q), C.minimo_pilha(ligar_pilha(p, fora))), corpo, teto), C.ContaLista{}, q, p, fora)
    case C.ContaRegistro{}:
      +q = {B.Numero64{a, b} : B.Numero64}
      abrir_conferido_ligado(C.conferir(C.somar_opcionais(C.minimo_campo(C.ContaRegistro{}, q), C.minimo_pilha(ligar_pilha(p, fora))), corpo, teto), C.ContaRegistro{}, q, p, fora)

def concluir_local_interno(+f: C.Finalidade, +a: U32, +b: U32, +p: C.Pilha, fora: C.Pilha,
  corpo: B.Numero64, teto: B.Numero64, interna: FinalidadeInterna(f, p)) -> Interna(concluir_local(f, a, b, p, fora, corpo, teto)):
  match f:
    case C.Inteiro{}:
      emitir_interno(p, D.VInt{a, b})
    case C.Texto{}:
      +q = {B.Numero64{a, b} : B.Numero64}
      abrir_conferido_interno(C.conferir(C.somar_opcionais(C.minimo_campo(C.Texto{}, q), C.minimo_pilha(ligar_pilha(p, fora))), corpo, teto), C.Texto{}, q, p, interna)
    case C.NomeTexto{}:
      +q = {B.Numero64{a, b} : B.Numero64}
      abrir_conferido_interno(C.conferir(C.somar_opcionais(C.minimo_campo(C.NomeTexto{}, q), C.minimo_pilha(ligar_pilha(p, fora))), corpo, teto), C.NomeTexto{}, q, p, interna)
    case C.ContaLista{}:
      +q = {B.Numero64{a, b} : B.Numero64}
      abrir_conferido_interno(C.conferir(C.somar_opcionais(C.minimo_campo(C.ContaLista{}, q), C.minimo_pilha(ligar_pilha(p, fora))), corpo, teto), C.ContaLista{}, q, p, interna)
    case C.ContaRegistro{}:
      +q = {B.Numero64{a, b} : B.Numero64}
      abrir_conferido_interno(C.conferir(C.somar_opcionais(C.minimo_campo(C.ContaRegistro{}, q), C.minimo_pilha(ligar_pilha(p, fora))), corpo, teto), C.ContaRegistro{}, q, p, interna)

def ler_local_ligado(n: Nat, +f: C.Finalidade, +a: U32, +b: U32, +x: U32,
  +p: C.Pilha, +fora: C.Pilha, +corpo: B.Numero64, +teto: B.Numero64) ->
  {ligar(ler_local(n, f, a, b, x, p, fora, corpo, teto), fora) == C.ler_palavra(n, f, a, b, x, ligar_pilha(p, fora), corpo, teto) : C.Maquina}:
  match n:
    case 0n:
      concluir_local_ligado(f, (a * 256 + U32.shrn(b, 24n) : U32), (b * 256 + x : U32), p, fora, corpo, teto)
    case 1n+k:
      {==}

def ler_local_interno(n: Nat, +f: C.Finalidade, a: U32, +b: U32, x: U32,
  +p: C.Pilha, fora: C.Pilha, corpo: B.Numero64, teto: B.Numero64,
  interna: FinalidadeInterna(f, p)) -> Interna(ler_local(n, f, a, b, x, p, fora, corpo, teto)):
  match n:
    case 0n:
      concluir_local_interno(f, (a * 256 + U32.shrn(b, 24n) : U32), (b * 256 + x : U32), p, fora, corpo, teto, interna)
    case 1n+k:
      interna

def ler_tag_ligado(n: Nat, +p: C.Pilha, +fora: C.Pilha) ->
  {ligar(C.ler_tag(n, p), fora) == C.ler_tag(n, ligar_pilha(p, fora)) : C.Maquina}:
  match n:
    case 0n:
      emitir_comuta_com_a_pilha_externa(p, fora, D.VAusente{})
    case 1n:
      emitir_comuta_com_a_pilha_externa(p, fora, D.VBool{False{}})
    case 2n:
      emitir_comuta_com_a_pilha_externa(p, fora, D.VBool{True{}})
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n+k:
      {==}

def ler_tag_interno(n: Nat, p: C.Pilha) -> Interna(C.ler_tag(n, p)):
  match n:
    case 0n:
      emitir_interno(p, D.VAusente{})
    case 1n:
      emitir_interno(p, D.VBool{False{}})
    case 2n:
      emitir_interno(p, D.VBool{True{}})
    case 3n:
      Unit{}
    case 4n:
      Unit{}
    case 5n:
      Unit{}
    case 6n:
      Unit{}
    case 7n+k:
      Unit{}

def ler_tag_nome_ligado(ok: Bool, +p: C.Pilha, +fora: C.Pilha) ->
  {ligar(C.ler_tag_nome(ok, p), fora) == C.ler_tag_nome(ok, ligar_pilha(p, fora)) : C.Maquina}:
  match ok:
    case False{}:
      {==}
    case True{}:
      {==}

def ler_tag_nome_interno(ok: Bool, +p: C.Pilha, interna: NaoRaiz(p)) -> Interna(C.ler_tag_nome(ok, p)):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      interna

law passo_local_ligado_e_o_passo_real:
  for +m: C.Maquina
  for +fora: C.Pilha
  for +b: U32
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for interna: Interna(m)
  for continua: Continua(m)
  {ligar(passo_local(m, fora, b, corpo, teto), fora) == C.passo(ligar(m, fora), b, corpo, teto) : C.Maquina}
def passo_local_ligado_e_o_passo_real(m, fora, b, corpo, teto, interna, continua):
  match m:
    case C.Tag{+p}:
      ler_tag_ligado(U32.to_nat(b), p, fora)
    case C.TagNome{+p}:
      ler_tag_nome_ligado(U32.is_eq(b, 4), p, fora)
    case C.Palavra{+f, +n, +a, +c, +p}:
      ler_local_ligado(n, f, a, c, b, p, fora, corpo, teto)
    case C.Conteudo{+nome, +ultimo, +q, +u, +s, +p}:
      guardar_escalar_ligado(C.passo_utf8(u, b), ultimo, nome, q, s, p, fora, interna)
    case C.Pronto{+v}:
      L.ex_falso({C.Invalido{} == C.passo(C.emitir(fora, v), b, corpo, teto) : C.Maquina}, continua)
    case C.Invalido{}:
      {==}
    case C.Acima{}:
      {==}

law passo_local_preserva_interior:
  for +m: C.Maquina
  for fora: C.Pilha
  for +b: U32
  for corpo: B.Numero64
  for teto: B.Numero64
  for interna: Interna(m)
  Interna(passo_local(m, fora, b, corpo, teto))
def passo_local_preserva_interior(m, fora, b, corpo, teto, interna):
  match m:
    case C.Tag{p}:
      ler_tag_interno(U32.to_nat(b), p)
    case C.TagNome{+p}:
      ler_tag_nome_interno(U32.is_eq(b, 4), p, interna)
    case C.Palavra{+f, n, a, c, +p}:
      ler_local_interno(n, f, a, c, b, p, fora, corpo, teto, interna)
    case C.Conteudo{+nome, ultimo, q, u, s, +p}:
      guardar_escalar_interno(C.passo_utf8(u, b), ultimo, nome, q, s, p, interna)
    case C.Pronto{v}:
      Unit{}
    case C.Invalido{}:
      Unit{}
    case C.Acima{}:
      Unit{}
