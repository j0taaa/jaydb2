import Base
import ./Bytes.bend as B
import ./Dados.bend as D
import ./Protocolo.bend as P

law utf8_multibyte:
  {B.utf8("Aç𝄞") == [65, 195, 167, 240, 157, 132, 158] : List<&2, U32>}
def utf8_multibyte():
  {==}

law utf8_maximo:
  {B.utf8_valido([244, 143, 191, 191]) == True{} : Bool}
def utf8_maximo():
  {==}

law utf8_overlong:
  {B.utf8_valido([192, 128]) == False{} : Bool}
def utf8_overlong():
  {==}

law utf8_surrogate:
  {B.utf8_valido([237, 160, 128]) == False{} : Bool}
def utf8_surrogate():
  {==}

law utf8_fora_do_dominio:
  {B.utf8_valido([244, 144, 128, 128]) == False{} : Bool}
def utf8_fora_do_dominio():
  {==}

law utf8_truncado:
  {B.utf8_valido([240, 159, 146]) == False{} : Bool}
def utf8_truncado():
  {==}

law utf8_nao_octeto:
  {B.utf8_valido([300]) == False{} : Bool}
def utf8_nao_octeto():
  {==}

law tamanho_u64:
  {B.comprimento64(3n) == Some{[0, 0, 0, 0, 0, 0, 0, 3]} : Maybe<&2, List<&2, U32>>}
def tamanho_u64():
  {==}

law transporte_u64:
  {B.incrementar64(Some{B.Numero64{0, 4294967295}}) == Some{B.Numero64{1, 0}} : Maybe<&2, B.Numero64>}
def transporte_u64():
  {==}

law overflow_u64:
  {B.incrementar64(Some{B.Numero64{4294967295, 4294967295}}) == None{} : Maybe<&2, B.Numero64>}
def overflow_u64():
  {==}

law ausencia_enquadrada:
  {P.enquadrar(D.VAusente{}) == Some{[0, 0, 0, 0, 0, 0, 0, 1, 0]} : Maybe<&2, List<&2, U32>>}
def ausencia_enquadrada():
  {==}

law lista_com_dois_itens:
  {P.codificar(D.VLista{D.VBool{False{}}, D.VLista{D.VAusente{}, D.VListaVazia{}}}) ==
   Some{[5, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0]} : Maybe<&2, List<&2, U32>>}
def lista_com_dois_itens():
  {==}

law rejeita_cauda_invalida:
  {P.codificar(D.VLista{D.VAusente{}, D.VBool{False{}}}) == None{} : Maybe<&2, List<&2, U32>>}
def rejeita_cauda_invalida():
  {==}

law rejeita_registro_duplicado:
  {P.codificar(D.VRegistro{"a", D.VAusente{}, D.VRegistro{"a", D.VAusente{}, D.VRegistroVazio{}}}) ==
   None{} : Maybe<&2, List<&2, U32>>}
def rejeita_registro_duplicado():
  {==}

law rejeita_registro_desordenado:
  {P.codificar(D.VRegistro{"b", D.VAusente{}, D.VRegistro{"a", D.VAusente{}, D.VRegistroVazio{}}}) ==
   None{} : Maybe<&2, List<&2, U32>>}
def rejeita_registro_desordenado():
  {==}

law erro_tem_valor_ausente:
  {P.resposta_valida(P.Resposta{P.Dados{}, D.VTexto{"interno"}}) == False{} : Bool}
def erro_tem_valor_ausente():
  {==}

law sucesso_pode_ter_resposta:
  {P.resposta_valida(P.Resposta{P.Sucesso{}, D.VTexto{"ok"}}) == True{} : Bool}
def sucesso_pode_ter_resposta():
  {==}
