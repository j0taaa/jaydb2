# Parte geral da Lei 2: validade de TODO valor realmente aceito pelo Codec.
# A equivalencia publica completa esta demonstrada em CodecLei2.bend.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecUnicode.bend as U
import ./CodecEstruturas.bend as E
import ./CodecPercurso.bend as R
import ./CodecCanonico.bend as K
import ../contrato/Protocolo.bend as P
import ./CodecContadores.bend as Contadores
import ./CodecUTF8.bend as UTF8
import ./CodecConteudo.bend as Conteudo
import ./CodecUTF8Bits.bend as BitsUTF8
import ./CodecPalavrasInversa.bend as Palavras
import ./CodecInteiros.bend as Inteiros
import ./CodecAridades.bend as Aridades

law nome_conferido_preserva_validade:
  for +ok: Bool
  for u: Bool
  for q: B.Numero64
  for +anterior: String
  for +nome: String
  for +xs: List<&2, D.Campo>
  for +pai: C.Pilha
  for campos: E.CamposInvertidos(xs)
  for ultimo: E.UltimoNome(xs, anterior)
  for acima: E.PilhaValida(pai)
  for confere: {ok == True{} : Bool} -> {D.nome_valido(nome) && String.is_lt(anterior, nome) == True{} : Bool}
  E.MaquinaValida(C.nome_conferido(ok, u, q, nome, xs, pai))
def nome_conferido_preserva_validade(ok, u, q, anterior, nome, xs, pai, campos, ultimo, acima, confere):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      +verificado = confere({==})
      L.Ambos{F.e_booleano_esquerda(D.nome_valido(nome), String.is_lt(anterior, nome), verificado),
        L.Ambos{E.campos_anteriores_ao_novo_nome(xs, anterior, nome, campos, ultimo,
          F.e_booleano_direita(D.nome_valido(nome), String.is_lt(anterior, nome), verificado)), acima}}

law emitir_nome_preserva_validade:
  for +pilha: C.Pilha
  for +nome: String
  for estrutura: E.PilhaValida(pilha)
  E.MaquinaValida(C.emitir_nome(pilha, nome))
def emitir_nome_preserva_validade(pilha, nome, estrutura):
  match pilha:
    case C.Nome{u, q, +anterior, +xs, +pai}:
      match estrutura:
        case L.Ambos{campos, L.Ambos{ultimo, acima}}:
          nome_conferido_preserva_validade(D.nome_valido(nome) && String.is_lt(anterior, nome), u, q, anterior, nome, xs, pai, campos, ultimo, acima, e => e)
    case C.Raiz{}:
      Unit{}
    case C.Lista{u, q, xs, pai}:
      Unit{}
    case C.Campo{u, q, n, xs, pai}:
      Unit{}

law emitir_texto_preserva_validade:
  for nome: Bool
  for +texto: String
  for +pilha: C.Pilha
  for estrutura: E.PilhaValida(pilha)
  for valido: {D.unicode_valido(texto) == True{} : Bool}
  E.MaquinaValida(C.emitir_texto(nome, texto, pilha))
def emitir_texto_preserva_validade(nome, texto, pilha, estrutura, valido):
  match nome:
    case False{}:
      E.emitir_preserva_validade(pilha, D.VTexto{texto}, estrutura, valido)
    case True{}:
      emitir_nome_preserva_validade(pilha, texto, estrutura)

law guardar_caractere_preserva_validade:
  for ultimo: Bool
  for nome: Bool
  for q: B.Numero64
  for +texto: String
  for +pilha: C.Pilha
  for estrutura: E.PilhaValida(pilha)
  for valido: {D.unicode_valido(texto) == True{} : Bool}
  E.MaquinaValida(C.guardar_caractere(ultimo, nome, q, texto, pilha))
def guardar_caractere_preserva_validade(ultimo, nome, q, texto, pilha, estrutura, valido):
  match ultimo:
    case True{}:
      emitir_texto_preserva_validade(nome, String.reverse(texto), pilha, estrutura, U.reverse_preserva_unicode(texto, valido))
    case False{}:
      L.Ambos{valido, estrutura}

law guardar_parcial_preserva_validade:
  for ultimo: Bool
  for nome: Bool
  for q: B.Numero64
  for u: C.Unicode
  for +texto: String
  for +pilha: C.Pilha
  for estrutura: E.PilhaValida(pilha)
  for valido: {D.unicode_valido(texto) == True{} : Bool}
  E.MaquinaValida(C.guardar_parcial(ultimo, nome, q, u, texto, pilha))
def guardar_parcial_preserva_validade(ultimo, nome, q, u, texto, pilha, estrutura, valido):
  match ultimo:
    case True{}:
      Unit{}
    case False{}:
      L.Ambos{valido, estrutura}

law guardar_escalar_preserva_validade:
  for +escalar: C.Escalar
  for ultimo: Bool
  for nome: Bool
  for q: B.Numero64
  for +texto: String
  for +pilha: C.Pilha
  for estrutura: E.PilhaValida(pilha)
  for valido: {D.unicode_valido(texto) == True{} : Bool}
  for cp_valido: U.EscalarValido(escalar)
  E.MaquinaValida(C.guardar_escalar(escalar, ultimo, nome, q, texto, pilha))
def guardar_escalar_preserva_validade(escalar, ultimo, nome, q, texto, pilha, estrutura, valido, cp_valido):
  match escalar:
    case C.UTFInvalido{}:
      Unit{}
    case C.Caractere{+cp}:
      guardar_caractere_preserva_validade(ultimo, nome, q, SCon{Chr{cp}, texto}, pilha, estrutura,
        F.e_booleano_intro(D.escalar_valido(cp), D.unicode_valido(texto), cp_valido, valido))
    case C.Parcial{u}:
      guardar_parcial_preserva_validade(ultimo, nome, q, u, texto, pilha, estrutura, valido)

law abrir_nome_preserva_validade:
  for cabe: Bool
  for n: B.Numero64
  for +pilha: C.Pilha
  for estrutura: E.PilhaValida(pilha)
  E.MaquinaValida(C.abrir_nome(cabe, n, pilha))
def abrir_nome_preserva_validade(cabe, n, pilha, estrutura):
  match cabe:
    case False{}:
      Unit{}
    case True{}:
      L.Ambos{{==}, estrutura}

law abrir_variavel_preserva_validade:
  for vazio: Bool
  for f: C.Finalidade
  for +n: B.Numero64
  for +pilha: C.Pilha
  for estrutura: E.PilhaValida(pilha)
  E.MaquinaValida(C.abrir_variavel(vazio, f, n, pilha))
def abrir_variavel_preserva_validade(vazio, f, n, pilha, estrutura):
  match vazio f:
    case True{} C.Texto{}:
      E.emitir_preserva_validade(pilha, D.VTexto{""}, estrutura, {==})
    case True{} C.ContaLista{}:
      E.emitir_preserva_validade(pilha, D.VListaVazia{}, estrutura, {==})
    case True{} C.ContaRegistro{}:
      E.emitir_preserva_validade(pilha, D.VRegistroVazio{}, estrutura, {==})
    case False{} C.Texto{}:
      L.Ambos{{==}, estrutura}
    case False{} C.NomeTexto{}:
      abrir_nome_preserva_validade(C.menor_igual64(n, B.Numero64{0, 64}), n, pilha, estrutura)
    case False{} C.ContaLista{}:
      L.Ambos{Unit{}, estrutura}
    case False{} C.ContaRegistro{}:
      L.Ambos{Unit{}, L.Ambos{Unit{}, estrutura}}
    case True{} C.Inteiro{}:
      Unit{}
    case True{} C.NomeTexto{}:
      Unit{}
    case False{} C.Inteiro{}:
      Unit{}

law abrir_conferido_preserva_validade:
  for conferencia: C.Conferencia
  for +f: C.Finalidade
  for +n: B.Numero64
  for +pilha: C.Pilha
  for estrutura: E.PilhaValida(pilha)
  E.MaquinaValida(C.abrir_conferido(conferencia, f, n, pilha))
def abrir_conferido_preserva_validade(conferencia, f, n, pilha, estrutura):
  match conferencia:
    case C.Grande{}:
      Unit{}
    case C.Curto{}:
      Unit{}
    case C.Cabe{}:
      abrir_variavel_preserva_validade(C.zero64(n), f, n, pilha, estrutura)

law concluir_palavra_preserva_validade:
  for f: C.Finalidade
  for +alto: U32
  for +baixo: U32
  for +pilha: C.Pilha
  for corpo: B.Numero64
  for teto: B.Numero64
  for estrutura: E.PilhaValida(pilha)
  E.MaquinaValida(C.concluir_palavra(f, alto, baixo, pilha, corpo, teto))
def concluir_palavra_preserva_validade(f, alto, baixo, pilha, corpo, teto, estrutura):
  match f:
    case C.Inteiro{}:
      E.emitir_preserva_validade(pilha, D.VInt{alto, baixo}, estrutura, {==})
    case C.Texto{}:
      +n = {B.Numero64{alto, baixo} : B.Numero64}
      abrir_conferido_preserva_validade(C.conferir(C.somar_opcionais(C.minimo_campo(C.Texto{}, n), C.minimo_pilha(pilha)), corpo, teto), C.Texto{}, n, pilha, estrutura)
    case C.NomeTexto{}:
      +n = {B.Numero64{alto, baixo} : B.Numero64}
      abrir_conferido_preserva_validade(C.conferir(C.somar_opcionais(C.minimo_campo(C.NomeTexto{}, n), C.minimo_pilha(pilha)), corpo, teto), C.NomeTexto{}, n, pilha, estrutura)
    case C.ContaLista{}:
      +n = {B.Numero64{alto, baixo} : B.Numero64}
      abrir_conferido_preserva_validade(C.conferir(C.somar_opcionais(C.minimo_campo(C.ContaLista{}, n), C.minimo_pilha(pilha)), corpo, teto), C.ContaLista{}, n, pilha, estrutura)
    case C.ContaRegistro{}:
      +n = {B.Numero64{alto, baixo} : B.Numero64}
      abrir_conferido_preserva_validade(C.conferir(C.somar_opcionais(C.minimo_campo(C.ContaRegistro{}, n), C.minimo_pilha(pilha)), corpo, teto), C.ContaRegistro{}, n, pilha, estrutura)

law ler_palavra_preserva_validade:
  for n: Nat
  for +f: C.Finalidade
  for +alto: U32
  for +baixo: U32
  for +b: U32
  for +pilha: C.Pilha
  for corpo: B.Numero64
  for teto: B.Numero64
  for estrutura: E.PilhaValida(pilha)
  E.MaquinaValida(C.ler_palavra(n, f, alto, baixo, b, pilha, corpo, teto))
def ler_palavra_preserva_validade(n, f, alto, baixo, b, pilha, corpo, teto, estrutura):
  match n:
    case 0n:
      concluir_palavra_preserva_validade(f, (alto * 256 + U32.shrn(baixo, 24n) : U32), (baixo * 256 + b : U32), pilha, corpo, teto, estrutura)
    case 1n+p:
      estrutura

law ler_tag_preserva_validade:
  for tag: Nat
  for +pilha: C.Pilha
  for estrutura: E.PilhaValida(pilha)
  E.MaquinaValida(C.ler_tag(tag, pilha))
def ler_tag_preserva_validade(tag, pilha, estrutura):
  match tag:
    case 0n:
      E.emitir_preserva_validade(pilha, D.VAusente{}, estrutura, {==})
    case 1n:
      E.emitir_preserva_validade(pilha, D.VBool{False{}}, estrutura, {==})
    case 2n:
      E.emitir_preserva_validade(pilha, D.VBool{True{}}, estrutura, {==})
    case 3n:
      estrutura
    case 4n:
      estrutura
    case 5n:
      estrutura
    case 6n:
      estrutura
    case 7n+p:
      Unit{}

law ler_tag_nome_preserva_validade:
  for correto: Bool
  for +pilha: C.Pilha
  for estrutura: E.PilhaValida(pilha)
  E.MaquinaValida(C.ler_tag_nome(correto, pilha))
def ler_tag_nome_preserva_validade(correto, pilha, estrutura):
  match correto:
    case False{}:
      Unit{}
    case True{}:
      estrutura

law passo_preserva_validade:
  for +m: C.Maquina
  for +b: U32
  for corpo: B.Numero64
  for teto: B.Numero64
  for estrutura: E.MaquinaValida(m)
  E.MaquinaValida(C.passo(m, b, corpo, teto))
def passo_preserva_validade(m, b, corpo, teto, estrutura):
  match m:
    case C.Tag{+pilha}:
      ler_tag_preserva_validade(U32.to_nat(b), pilha, estrutura)
    case C.TagNome{+pilha}:
      ler_tag_nome_preserva_validade(U32.is_eq(b, 4), pilha, estrutura)
    case C.Palavra{f, n, alto, baixo, +pilha}:
      ler_palavra_preserva_validade(n, f, alto, baixo, b, pilha, corpo, teto, estrutura)
    case C.Conteudo{nome, ultimo, q, +u, +texto, +pilha}:
      match estrutura:
        case L.Ambos{valido, pilha_valida}:
          guardar_escalar_preserva_validade(C.passo_utf8(u, b), ultimo, nome, q, texto, pilha, pilha_valida, valido, U.passo_utf8_so_emite_escalares_validos(u, b))
    case C.Pronto{v}:
      Unit{}
    case C.Invalido{}:
      Unit{}
    case C.Acima{}:
      Unit{}

def ResultadoValido(r: C.Resultado) -> Type:
  match r:
    case C.Decodificado{v}:
      {D.valor_valido(v) == True{} : Bool}
    case _:
      Unit

law finalizar_preserva_validade:
  for +m: C.Maquina
  for estrutura: E.MaquinaValida(m)
  ResultadoValido(C.finalizar(m))
def finalizar_preserva_validade(m, estrutura):
  match m:
    case C.Tag{pilha}:
      Unit{}
    case C.TagNome{pilha}:
      Unit{}
    case C.Palavra{f, n, a, b, pilha}:
      Unit{}
    case C.Conteudo{nome, ultimo, q, u, texto, pilha}:
      Unit{}
    case C.Pronto{v}:
      estrutura
    case C.Invalido{}:
      Unit{}
    case C.Acima{}:
      Unit{}

law percorrer_preserva_validade:
  for bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +m: C.Maquina
  for estrutura: E.MaquinaValida(m)
  ResultadoValido(C.percorrer(bs, corpo, teto, m))
def percorrer_preserva_validade(bs, corpo, teto, m, estrutura):
  match bs:
    case Nil{}:
      finalizar_preserva_validade(m, estrutura)
    case Con{+b, t}:
      +resto = C.diminuir64(corpo)
      +livre = C.diminuir64(teto)
      percorrer_preserva_validade(t, resto, livre, C.passo(m, b, resto, livre), passo_preserva_validade(m, b, resto, livre, estrutura))

law decodificar_octetos_preserva_validade:
  for validos: Bool
  for bs: List<&2, U32>
  for corpo: B.Numero64
  for teto: B.Numero64
  ResultadoValido(C.decodificar_octetos(validos, bs, corpo, teto))
def decodificar_octetos_preserva_validade(validos, bs, corpo, teto):
  match validos:
    case False{}:
      Unit{}
    case True{}:
      percorrer_preserva_validade(bs, corpo, teto, C.Tag{C.Raiz{}}, Unit{})

law decodificar_tamanho_preserva_validade:
  for cabe: Bool
  for +bs: List<&2, U32>
  for corpo: B.Numero64
  for teto: B.Numero64
  ResultadoValido(C.decodificar_tamanho(cabe, bs, corpo, teto))
def decodificar_tamanho_preserva_validade(cabe, bs, corpo, teto):
  match cabe:
    case False{}:
      Unit{}
    case True{}:
      decodificar_octetos_preserva_validade(B.octetos_validos(bs), bs, corpo, teto)

law decodificar_medida_preserva_validade:
  for n: Maybe<&2, B.Numero64>
  for bs: List<&2, U32>
  for +teto: B.Numero64
  ResultadoValido(C.decodificar_medida(n, bs, teto))
def decodificar_medida_preserva_validade(n, bs, teto):
  match n:
    case None{}:
      Unit{}
    case Some{+corpo}:
      decodificar_tamanho_preserva_validade(C.menor_igual64(corpo, teto), bs, corpo, teto)

law decodificar_so_devolve_valor_valido:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for -v: D.Valor
  for aceito: {C.decodificar(bs, teto) == C.Decodificado{v} : C.Resultado}
  {D.valor_valido(v) == True{} : Bool}
def decodificar_so_devolve_valor_valido(bs, teto, v, aceito):
  %aceito : ResultadoValido(_)
  decodificar_medida_preserva_validade(B.nat64(B.comprimento(bs)), bs, teto)

# Reune as garantias efetivamente provadas; nao contem uma premissa Canonico.
type AceitacaoComprovada<-bs: List<&2, U32>, -teto: B.Numero64, -v: D.Valor> is Type:
  Aceitacao{corpo: B.Numero64,
    medida: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>},
    cabe: {C.menor_igual64(corpo, teto) == True{} : Bool},
    octetos: {B.octetos_validos(bs) == True{} : Bool},
    terminal: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})) == C.Pronto{v} : C.Maquina},
    valido: {D.valor_valido(v) == True{} : Bool}}

def reunir_aceitacao(+bs: List<&2, U32>, +teto: B.Numero64, -v: D.Valor,
  conferida: R.EntradaConferida<B.nat64(B.comprimento(bs)), bs, teto, v>,
  valido: {D.valor_valido(v) == True{} : Bool}) -> AceitacaoComprovada<bs, teto, v>:
  match conferida:
    case R.Conferida{+corpo, medida, cabe, octetos, percurso}:
      Aceitacao{corpo, medida, cabe, octetos,
        R.percurso_aceito_termina_pronto(bs, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}}, v, percurso), valido}

law aceitacao_garante_validade_limite_e_consumo_integral:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for -v: D.Valor
  for +aceito: {C.decodificar(bs, teto) == C.Decodificado{v} : C.Resultado}
  AceitacaoComprovada<bs, teto, v>
def aceitacao_garante_validade_limite_e_consumo_integral(bs, teto, v, aceito):
  reunir_aceitacao(bs, teto, v,
    R.aceitacao_exige_corpo_representavel_octetos_e_limite(bs, teto, v, aceito),
    decodificar_so_devolve_valor_valido(bs, teto, v, aceito))

law valor_aceito_libera_encoder_original:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for +v: D.Valor
  for aceito: {C.decodificar(bs, teto) == C.Decodificado{v} : C.Resultado}
  {P.codificar(v) == P.finalizar(P.codificar_parcial(v)) : Maybe<&2, List<&2, U32>>}
def valor_aceito_libera_encoder_original(bs, teto, v, aceito):
  K.valor_valido_libera_codificacao(v, decodificar_so_devolve_valor_valido(bs, teto, v, aceito))
