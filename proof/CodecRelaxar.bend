# Retirar a pilha externa de uma execucao LOCAL aceita preserva exatamente
# todos os estados e contadores. So os guards da Palavra podem divergir;
# sua aceitacao e extraida do sufixo, e o minimo menor e provado separado.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecPercurso.bend as R
import ./CodecAceitacaoPilha.bend as J
import ./CodecAceitacaoPrefixo.bend as P
import ./CodecRelaxarAritmetica.bend as A

law erro_local_invalido_absorvente:
  for bs: List<&2, U32>
  for +fora: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  {R.maquina(P.executar_local(bs, fora, R.Quadro{corpo, teto, C.Invalido{}})) == C.Invalido{} : C.Maquina}
def erro_local_invalido_absorvente(bs, fora, corpo, teto):
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      erro_local_invalido_absorvente(t, fora, C.diminuir64(corpo), C.diminuir64(teto))

law erro_local_acima_absorvente:
  for bs: List<&2, U32>
  for +fora: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  {R.maquina(P.executar_local(bs, fora, R.Quadro{corpo, teto, C.Acima{}})) == C.Acima{} : C.Maquina}
def erro_local_acima_absorvente(bs, fora, corpo, teto):
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      erro_local_acima_absorvente(t, fora, C.diminuir64(corpo), C.diminuir64(teto))

law conferencia_local_aceita_exige_cabe:
  for c: C.Conferencia
  for +bs: List<&2, U32>
  for +fora: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +f: C.Finalidade
  for +q: B.Numero64
  for +p: C.Pilha
  for -v: D.Valor
  for aceito: {R.maquina(P.executar_local(bs, fora, R.Quadro{corpo, teto, C.abrir_conferido(c, f, q, p)})) == C.Pronto{v} : C.Maquina}
  {c == C.Cabe{} : C.Conferencia}
def conferencia_local_aceita_exige_cabe(c, bs, fora, corpo, teto, f, q, p, v, aceito):
  match c:
    case C.Cabe{}:
      {==}
    case C.Curto{}:
      L.ex_falso({C.Curto{} == C.Cabe{} : C.Conferencia}, R.entrada_nao_decodificada(v,
        Equal.cong(C.Maquina, C.Resultado, m => C.finalizar(m), C.Invalido{}, C.Pronto{v},
          Equal.trans(C.Maquina, C.Invalido{}, R.maquina(P.executar_local(bs, fora, R.Quadro{corpo, teto, C.Invalido{}})), C.Pronto{v},
            Equal.sym(C.Maquina, R.maquina(P.executar_local(bs, fora, R.Quadro{corpo, teto, C.Invalido{}})), C.Invalido{}, erro_local_invalido_absorvente(bs, fora, corpo, teto)), aceito))))
    case C.Grande{}:
      L.ex_falso({C.Grande{} == C.Cabe{} : C.Conferencia}, R.limite_nao_decodificado(v,
        Equal.cong(C.Maquina, C.Resultado, m => C.finalizar(m), C.Acima{}, C.Pronto{v},
          Equal.trans(C.Maquina, C.Acima{}, R.maquina(P.executar_local(bs, fora, R.Quadro{corpo, teto, C.Acima{}})), C.Pronto{v},
            Equal.sym(C.Maquina, R.maquina(P.executar_local(bs, fora, R.Quadro{corpo, teto, C.Acima{}})), C.Acima{}, erro_local_acima_absorvente(bs, fora, corpo, teto)), aceito))))

def conferir_completo(+f: C.Finalidade, +q: B.Numero64, +p: C.Pilha, +fora: C.Pilha,
  corpo: B.Numero64, teto: B.Numero64) -> C.Conferencia:
  C.conferir(C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(J.ligar_pilha(p, fora))), corpo, teto)

def retirar_guard_aceito(+f: C.Finalidade, +q: B.Numero64, +p: C.Pilha, +fora: C.Pilha,
  +corpo: B.Numero64, +teto: B.Numero64, +bs: List<&2, U32>, -v: D.Valor,
  aceito: {R.maquina(P.executar_local(bs, fora, R.Quadro{corpo, teto, C.abrir_conferido(conferir_completo(f, q, p, fora, corpo, teto), f, q, p)})) == C.Pronto{v} : C.Maquina}) ->
  {C.abrir_conferido(C.conferir(C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(p)), corpo, teto), f, q, p) ==
    C.abrir_conferido(conferir_completo(f, q, p, fora, corpo, teto), f, q, p) : C.Maquina}:
  +cabe_fora = conferencia_local_aceita_exige_cabe(conferir_completo(f, q, p, fora, corpo, teto), bs, fora, corpo, teto, f, q, p, v, aceito)
  cabe_raiz = A.conferir_sem_pilha_externa(f, q, p, fora, corpo, teto, cabe_fora)
  Equal.trans(C.Maquina,
    C.abrir_conferido(C.conferir(C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(p)), corpo, teto), f, q, p),
    C.abrir_conferido(C.Cabe{}, f, q, p), C.abrir_conferido(conferir_completo(f, q, p, fora, corpo, teto), f, q, p),
    Equal.cong(C.Conferencia, C.Maquina, c => C.abrir_conferido(c, f, q, p), C.conferir(C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(p)), corpo, teto), C.Cabe{}, cabe_raiz),
    Equal.cong(C.Conferencia, C.Maquina, c => C.abrir_conferido(c, f, q, p), C.Cabe{}, conferir_completo(f, q, p, fora, corpo, teto),
      Equal.sym(C.Conferencia, conferir_completo(f, q, p, fora, corpo, teto), C.Cabe{}, cabe_fora)))

def concluir_local_retirar_fora(+f: C.Finalidade, +alto: U32, +baixo: U32, +p: C.Pilha, +fora: C.Pilha,
  +corpo: B.Numero64, +teto: B.Numero64, +bs: List<&2, U32>, -v: D.Valor,
  aceito: {R.maquina(P.executar_local(bs, fora, R.Quadro{corpo, teto, J.concluir_local(f, alto, baixo, p, fora, corpo, teto)})) == C.Pronto{v} : C.Maquina}) ->
  {C.concluir_palavra(f, alto, baixo, p, corpo, teto) == J.concluir_local(f, alto, baixo, p, fora, corpo, teto) : C.Maquina}:
  match f:
    case C.Inteiro{}:
      {==}
    case C.Texto{}:
      retirar_guard_aceito(C.Texto{}, B.Numero64{alto, baixo}, p, fora, corpo, teto, bs, v, aceito)
    case C.NomeTexto{}:
      retirar_guard_aceito(C.NomeTexto{}, B.Numero64{alto, baixo}, p, fora, corpo, teto, bs, v, aceito)
    case C.ContaLista{}:
      retirar_guard_aceito(C.ContaLista{}, B.Numero64{alto, baixo}, p, fora, corpo, teto, bs, v, aceito)
    case C.ContaRegistro{}:
      retirar_guard_aceito(C.ContaRegistro{}, B.Numero64{alto, baixo}, p, fora, corpo, teto, bs, v, aceito)

law passo_local_aceito_e_passo_real_sem_pilha_externa:
  for +m: C.Maquina
  for +fora: C.Pilha
  for +b: U32
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +bs: List<&2, U32>
  for -v: D.Valor
  for aceito: {R.maquina(P.executar_local(bs, fora, R.Quadro{corpo, teto, J.passo_local(m, fora, b, corpo, teto)})) == C.Pronto{v} : C.Maquina}
  {C.passo(m, b, corpo, teto) == J.passo_local(m, fora, b, corpo, teto) : C.Maquina}
def passo_local_aceito_e_passo_real_sem_pilha_externa(m, fora, b, corpo, teto, bs, v, aceito):
  match m:
    case C.Tag{p}:
      {==}
    case C.TagNome{p}:
      {==}
    case C.Palavra{+f, 0n, +alto, +baixo, +p}:
      concluir_local_retirar_fora(f, (alto * 256 + U32.shrn(baixo, 24n) : U32), (baixo * 256 + b : U32), p, fora, corpo, teto, bs, v, aceito)
    case C.Palavra{f, 1n+n, alto, baixo, p}:
      {==}
    case C.Conteudo{nome, ultimo, q, u, s, p}:
      {==}
    case C.Pronto{w}:
      {==}
    case C.Invalido{}:
      {==}
    case C.Acima{}:
      {==}

law execucao_local_aceita_coincide_com_execucao_real:
  for +bs: List<&2, U32>
  for +fora: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +m: C.Maquina
  for -v: D.Valor
  for +aceito: {R.maquina(P.executar_local(bs, fora, R.Quadro{corpo, teto, m})) == C.Pronto{v} : C.Maquina}
  {R.executar(bs, R.Quadro{corpo, teto, m}) == P.executar_local(bs, fora, R.Quadro{corpo, teto, m}) : R.Quadro}
def execucao_local_aceita_coincide_com_execucao_real(bs, fora, corpo, teto, m, v, aceito):
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      +resto = C.diminuir64(corpo)
      +livre = C.diminuir64(teto)
      %Equal.sym(C.Maquina, C.passo(m, b, resto, livre), J.passo_local(m, fora, b, resto, livre),
        passo_local_aceito_e_passo_real_sem_pilha_externa(m, fora, b, resto, livre, t, v, aceito)) :
        {R.executar(t, R.Quadro{resto, livre, _}) == P.executar_local(t, fora, R.Quadro{resto, livre, J.passo_local(m, fora, b, resto, livre)}) : R.Quadro}
      execucao_local_aceita_coincide_com_execucao_real(t, fora, resto, livre, J.passo_local(m, fora, b, resto, livre), v, aceito)

law execucao_local_aceita_continua_aceita_sem_pilha_externa:
  for +bs: List<&2, U32>
  for +fora: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +m: C.Maquina
  for -v: D.Valor
  for +aceito: {R.maquina(P.executar_local(bs, fora, R.Quadro{corpo, teto, m})) == C.Pronto{v} : C.Maquina}
  {R.maquina(R.executar(bs, R.Quadro{corpo, teto, m})) == C.Pronto{v} : C.Maquina}
def execucao_local_aceita_continua_aceita_sem_pilha_externa(bs, fora, corpo, teto, m, v, aceito):
  Equal.trans(C.Maquina,
    R.maquina(R.executar(bs, R.Quadro{corpo, teto, m})), R.maquina(P.executar_local(bs, fora, R.Quadro{corpo, teto, m})), C.Pronto{v},
    Equal.cong(R.Quadro, C.Maquina, q => R.maquina(q), R.executar(bs, R.Quadro{corpo, teto, m}), P.executar_local(bs, fora, R.Quadro{corpo, teto, m}),
      execucao_local_aceita_coincide_com_execucao_real(bs, fora, corpo, teto, m, v, aceito)), aceito)
