# Invariantes de listas, registros e pilhas de src/Codec, sem teto estrutural.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F

# Cada elemento ja lido e valido. Nao se exige um tamanho Nat/u64 fixo.
def ValoresValidos(xs: List<&2, D.Valor>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{h, t}:
      L.E<{D.valor_valido(h) == True{} : Bool}, ValoresValidos(t)>

# A pilha guarda campos na ordem inversa de leitura. A fronteira e estrita.
def CamposAntes(xs: List<&2, D.Campo>, seguinte: String) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{D.Campo{n, v}, t}:
      L.E<{D.nome_valido(n) == True{} : Bool},
        L.E<{D.valor_valido(v) == True{} : Bool},
          L.E<{String.is_lt(n, seguinte) == True{} : Bool}, CamposAntes(t, n)>>>

def CamposInvertidos(xs: List<&2, D.Campo>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{D.Campo{n, v}, t}:
      L.E<{D.nome_valido(n) == True{} : Bool},
        L.E<{D.valor_valido(v) == True{} : Bool}, CamposAntes(t, n)>>

# Liga anterior ao campo efetivamente acumulado; vazio nao inventa um nome.
def UltimoNome(xs: List<&2, D.Campo>, anterior: String) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{D.Campo{n, v}, t}:
      {n == anterior : String}

law montar_lista_preserva_forma:
  for xs: List<&2, D.Valor>
  for +acc: D.Valor
  for forma: {D.eh_lista(acc) == True{} : Bool}
  {D.eh_lista(C.montar_lista(xs, acc)) == True{} : Bool}
def montar_lista_preserva_forma(xs, acc, forma):
  match xs:
    case Nil{}:
      forma
    case Con{h, t}:
      montar_lista_preserva_forma(t, D.VLista{h, acc}, {==})

law montar_lista_preserva_validade:
  for +xs: List<&2, D.Valor>
  for +acc: D.Valor
  for elementos: ValoresValidos(xs)
  for forma: {D.eh_lista(acc) == True{} : Bool}
  for valida: {D.valor_valido(acc) == True{} : Bool}
  {D.valor_valido(C.montar_lista(xs, acc)) == True{} : Bool}
def montar_lista_preserva_validade(xs, acc, elementos, forma, valida):
  match xs:
    case Nil{}:
      valida
    case Con{+h, t}:
      match elementos:
        case L.Ambos{cabeca, cauda}:
          montar_lista_preserva_validade(t, D.VLista{h, acc}, cauda, {==},
            F.e_booleano_intro(D.valor_valido(h) && D.eh_lista(acc), D.valor_valido(acc),
              F.e_booleano_intro(D.valor_valido(h), D.eh_lista(acc), cabeca, forma), valida))

law montar_registro_preserva_forma:
  for xs: List<&2, D.Campo>
  for +acc: D.Valor
  for forma: {D.eh_registro(acc) == True{} : Bool}
  {D.eh_registro(C.montar_registro(xs, acc)) == True{} : Bool}
def montar_registro_preserva_forma(xs, acc, forma):
  match xs:
    case Nil{}:
      forma
    case Con{D.Campo{n, v}, t}:
      montar_registro_preserva_forma(t, D.VRegistro{n, v, acc}, {==})

law montar_registro_apos_cabeca:
  for +xs: List<&2, D.Campo>
  for +n: String
  for +v: D.Valor
  for +r: D.Valor
  for campos: CamposAntes(xs, n)
  for valida: {D.valor_valido(D.VRegistro{n, v, r}) == True{} : Bool}
  {D.valor_valido(C.montar_registro(xs, D.VRegistro{n, v, r})) == True{} : Bool}
def montar_registro_apos_cabeca(xs, n, v, r, campos, valida):
  match xs:
    case Nil{}:
      valida
    case Con{D.Campo{+anterior, +valor}, t}:
      match campos:
        case L.Ambos{nome, L.Ambos{dado, L.Ambos{ordem, cauda}}}:
          montar_registro_apos_cabeca(t, anterior, valor, D.VRegistro{n, v, r}, cauda,
            F.e_booleano_intro(D.nome_valido(anterior) && D.valor_valido(valor) && String.is_lt(anterior, n), D.valor_valido(D.VRegistro{n, v, r}),
              F.e_booleano_intro(D.nome_valido(anterior) && D.valor_valido(valor), String.is_lt(anterior, n),
                F.e_booleano_intro(D.nome_valido(anterior), D.valor_valido(valor), nome, dado), ordem), valida))

law montar_registro_preserva_validade:
  for +xs: List<&2, D.Campo>
  for campos: CamposInvertidos(xs)
  {D.valor_valido(C.montar_registro(xs, D.VRegistroVazio{})) == True{} : Bool}
def montar_registro_preserva_validade(xs, campos):
  match xs:
    case Nil{}:
      {==}
    case Con{D.Campo{+n, +v}, t}:
      match campos:
        case L.Ambos{nome, L.Ambos{valor, cauda}}:
          montar_registro_apos_cabeca(t, n, v, D.VRegistroVazio{}, cauda,
            F.e_booleano_intro(D.nome_valido(n) && D.valor_valido(v) && True{}, True{},
              F.e_booleano_intro(D.nome_valido(n) && D.valor_valido(v), True{},
                F.e_booleano_intro(D.nome_valido(n), D.valor_valido(v), nome, valor), {==}), {==}))

law campos_anteriores_ao_novo_nome:
  for +xs: List<&2, D.Campo>
  for +anterior: String
  for +nome: String
  for campos: CamposInvertidos(xs)
  for ultimo: UltimoNome(xs, anterior)
  for ordem: {String.is_lt(anterior, nome) == True{} : Bool}
  CamposAntes(xs, nome)
def campos_anteriores_ao_novo_nome(xs, anterior, nome, campos, ultimo, ordem):
  match xs:
    case Nil{}:
      Unit{}
    case Con{D.Campo{+n, +v}, t}:
      match campos:
        case L.Ambos{valido, L.Ambos{valor, cauda}}:
          L.Ambos{valido, L.Ambos{valor, L.Ambos{
            (%Equal.sym(String, n, anterior, ultimo) : {String.is_lt(_, nome) == True{} : Bool}
              ordem), cauda}}}

def PilhaValida(pilha: C.Pilha) -> Type:
  match pilha:
    case C.Raiz{}:
      Unit
    case C.Lista{u, q, xs, pai}:
      L.E<ValoresValidos(xs), PilhaValida(pai)>
    case C.Nome{u, q, anterior, xs, pai}:
      L.E<CamposInvertidos(xs), L.E<UltimoNome(xs, anterior), PilhaValida(pai)>>
    case C.Campo{u, q, nome, xs, pai}:
      L.E<{D.nome_valido(nome) == True{} : Bool}, L.E<CamposAntes(xs, nome), PilhaValida(pai)>>

def MaquinaValida(m: C.Maquina) -> Type:
  match m:
    case C.Tag{pilha}:
      PilhaValida(pilha)
    case C.TagNome{pilha}:
      PilhaValida(pilha)
    case C.Palavra{f, n, a, b, pilha}:
      PilhaValida(pilha)
    case C.Conteudo{nome, ultimo, q, u, texto, pilha}:
      L.E<{D.unicode_valido(texto) == True{} : Bool}, PilhaValida(pilha)>
    case C.Pronto{v}:
      {D.valor_valido(v) == True{} : Bool}
    case C.Invalido{}:
      Unit
    case C.Acima{}:
      Unit

law emitir_preserva_validade:
  for +pilha: C.Pilha
  for +valor: D.Valor
  for estrutura: PilhaValida(pilha)
  for valido: {D.valor_valido(valor) == True{} : Bool}
  MaquinaValida(C.emitir(pilha, valor))
def emitir_preserva_validade(pilha, valor, estrutura, valido):
  match pilha:
    case C.Raiz{}:
      valido
    case C.Lista{True{}, q, +xs, +pai}:
      match estrutura:
        case L.Ambos{elementos, acima}:
          emitir_preserva_validade(pai, C.montar_lista(Con{valor, xs}, D.VListaVazia{}), acima,
            montar_lista_preserva_validade(Con{valor, xs}, D.VListaVazia{}, L.Ambos{valido, elementos}, {==}, {==}))
    case C.Lista{False{}, q, xs, pai}:
      match estrutura:
        case L.Ambos{elementos, acima}:
          L.Ambos{L.Ambos{valido, elementos}, acima}
    case C.Campo{True{}, q, +nome, +xs, +pai}:
      match estrutura:
        case L.Ambos{nome_valido, L.Ambos{campos, acima}}:
          emitir_preserva_validade(pai, C.montar_registro(Con{D.Campo{nome, valor}, xs}, D.VRegistroVazio{}), acima,
            montar_registro_preserva_validade(Con{D.Campo{nome, valor}, xs}, L.Ambos{nome_valido, L.Ambos{valido, campos}}))
    case C.Campo{False{}, q, nome, xs, pai}:
      match estrutura:
        case L.Ambos{nome_valido, L.Ambos{campos, acima}}:
          L.Ambos{L.Ambos{nome_valido, L.Ambos{valido, campos}}, L.Ambos{{==}, acima}}
    case C.Nome{u, q, nome, xs, pai}:
      Unit{}
