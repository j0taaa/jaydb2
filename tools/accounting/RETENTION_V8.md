# Retenção V8: lifecycle e wrappers de marcador

A [revisão independente V7](../../tests/accounting/review_v7/REPORT.txt) confirmou
os dois reparos numéricos anteriores e encontrou R7-1, uma corrida local de
progresso sob SIGKILL. O [desenho e a auditoria ptrace](PTRACE_AUDIT_V8.md)
documentam a reprodução anterior ao rebuild, reconciliação sem zerar owners e
limites adjacentes. Não se alteraram V3–V7, seus manifests/evidências/validações,
históricos, originais18 ou CLOSURE. O resultado V7 de 72 métodos foi copiado
literalmente para history/RESULTS_V7_72_TESTS.json antes dos novos testes.

## Token residual em getpid

Durante a regressão de morte em hold, um getpid ordinário após
window_end_until expirado repetiu involuntariamente o marcador e fechou o
scope inicial: syscall getpid não possui argumentos e a libc podia conservar
RDI=JAYACCT_MARKER do wrapper anterior. O relatório bruto e a saída da falha
ficam na evidência V8; não foi uma nova syscall solicitada pelo fixture.

Somente counter.c e deadline.h foram corrigidos nessa frente, por autorização
expressa do usuário. Após validar errno/ABI/recibo, todos os caminhos de retorno
de um marcador executado fazem xor edi,edi. O valor de retorno é operando
read/write de EAX da última asm; RDI, cc e memory são clobbers. Isso ordena a
validação antes da limpeza, inclusive comparação do recibo op6 com o próprio
token, e força a recarga de token em outro marcador inline explícito. RDI é
caller-saved: não se promete o valor após trabalho posterior do caller nem se
presume o comportamento de wrappers raw6 privados de outra frente.

O wrapper inline continua sem libc, alocador, errno store, loop ou remarcação
de tempo. Emissão efetiva das variantes op0/op5/op6/until e operação dinâmica
foi verificada em -O2/-O3: syscall único, nenhum call, limpeza final em cada
retorno após validação de recibo/erro. Os artefatos .s e o binário/disassembly
são conservados para revisão. Testes reais chamam getpid imediatamente após
marcadores C e inline, consecutivos, êxito/erro, deadline passado, op6 com e sem
hold e fora do tracer. Sob hold, uma leitura do contador verifica que getpid
não publicou sequência extra; fora do hold, o estado do scope é conferido.

Cleanup não publica fato Campo/tempo. ETIMEDOUT continua invalidando a saída;
o probe verifica o C-clock antes do release de hold e não emite Campo. Continuam com
o caller/ROOT as obrigações de relógio antes de publicação, comprimento,
barreira final, stack explícita preativa, sinais mascarados e stores sem
alocação antes de liberar hold. ABI counter120/window280 e op6 sem scan estão
intactos; o modo genérico e --service-window permanecem com a mesma API.

Header deadline.h estabilizado em
`33acf1a236f31bedd64e3a6a265cc1fa187ee8770fb6e5eca6139966a082e15f`.
ROOT foi avisado para pinagem de seu novo nativeV2. ServiceV2/EXTRATO78 usam
header anterior congelado: não foram editados nem associados a este header
live por suposição. ROOT fará atualização de dependência e revalidação de
Root/Receiver/Field em sua própria frente depois da entrega e nova revisão.

## Execução e evidência

```sh
python3 -B tests/accounting/test_accounting.py -v
python3 -B tools/accounting/replay_v7_review.py
```

Sete métodos novos preservam os 72 anteriores literalmente no AST. Cobrem a
reprodução original com/sem report e controles, resultado comprometido em EXIT,
referências privadas/COW independentes, morte no hold com janela inicial,
deadline, cleanup e emissão otimizada. O comparador pareado usa o mesmo fixture
binário sob V7/current; compila o counter desse fixture a partir de V7 para que
o reparo dos wrappers não seja uma variável escondida nessa comparação.
A suíte normal compila todos os fixtures com as fontes atuais. A amostragem
do erro antigo é intermitente; frequências são observações, não probabilidade
universal ou condição artificial para aceitar um teste.

Passaram 79/79 métodos, 422 registros, em 27,533765870 s. Os 108 runs pareados
e de controle registram V7 kill 4/24 abortos com report e 2/24 sem report;
current kill 24/24 com report e 24/24 sem concluem. Os 12 controles livres/exec
concluem. Antes do rebuild, a reprodução separada já havia registrado os
3/24 e 2/24 abortos citados na auditoria. Fontes e artefatos default da suíte
coincidem exatamente com o build current do comparador causal. Os 201 caminhos
históricos protegidos, originais18 e 2343 arquivos do índice da revisão foram
conferidos intactos antes do novo freeze.

RESULTS.json, REVIEW_V7_RESULTS.json e os novos manifest/evidence/validation V8
registram contagens, hashes, logs e resultados. A validação recompila somente
a extração e confere igualdade com fontes live, preservação dos históricos e
proveniência/somas de todos os JSONLs incluídos, inclusive prefixos sem summary
dos abortos antigos. CLOSURE global fica provisório e fora desse freeze.

## INCOMPLETE permanece

Não há nova divergência numérica demonstrada por R7-1, nem prova de alcance ou
ausência desse caminho no DB. Os reparos locais não certificam MedicaoReal,
Lei 2, Contrato ou AlocouCampo. Continuam abertos leases de objetos adaptados
ou com views, TOCTOU de path/open_how/dirfd/mount/procfs, metadados ptrace
indispensáveis descritos na auditoria, imported/special/hugetlb payloads,
generic fault/COW/invalidação, prefixo bootstrap estático, contrato do kernel,
K/watchdog, Campo, Sem_Ctx e fechamento final das entradas/host/CLI/framing.
Os avanços de service/receiving/decoder/recipe/Field comunicados por ROOT não
foram revalidados nem promovidos aqui a fechamento integral. Nenhuma lei,
quota, filtro de Processavel ou recurso excluído da medida foi introduzido.
É necessária uma NOVA task independente de ROOT sobre o V8 entregue.
