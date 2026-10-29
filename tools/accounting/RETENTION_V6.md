# Retenção V6 após a revisão independente V5

Os dois achados locais R5-1/R5-2 foram reproduzidos antes das alterações, com
controle livre concluído e V5 bloqueado nos limites de limpeza com/sem report.
O [relatório e fixtures V5](../../tests/accounting/review_v5/REPORT.txt) foram
preservados literalmente; PRESERVED.json identifica as cópias e o índice original
ARTIFACT_SHA256.json conserva os hashes da revisão inteira. Nenhum arquivo da
árvore original de revisão foi alterado. RESULTS V5 foi copiado literalmente
para history/RESULTS_V5_52_TESTS.json antes da atualização corrente.

## Resolução contextual e progresso

**R5-2.** O walker de caminhos ordinários passa a receber a política O_NOFOLLOW.
Ele continua traduzindo procfs self para TGID e thread-self para TGID/task/TID
reais e seguindo magic links intermediários no kernel. O_NOFOLLOW impede seguir
somente o componente final; não desvia mais o caminho inteiro para um open
auxiliar cujo self pertencia ao observer. Um symlink final continua sendo symlink
na consulta O_PATH, e o open real sem O_PATH falha com ELOOP. O_TRUNC ignorado em
FIFO não ocupa o slot exclusivo. RESOLVE_IN_ROOT conserva o caminho de resolução
pelo kernel com o dirfd real e symlinks absolutos relativos à raiz fornecida.
Isso não resolve genericamente procfs contextual com todos os resolve/mount/IDs.

**R5-1 e causa adjacente.** A exclusão passa a depender também da identidade
representada, tanto para truncate(path) quanto para open/openat/openat2/creat
truncantes. Se a consulta real identifica um alvo sem objeto adaptado e sem view
file-backed na observação, alterações de conteúdo do arquivo comum não modificam
esse ledger de backing userspace. A operação pode esperar por SIGIO/F_SETLEASE
no peer. Page cache de arquivo comum não recebe payload inventado.

Um memfd conhecido ou outro objeto representado continua exclusivo. Views
compartilhadas e privadas/COW existentes também conservam a exclusão, mesmo
quando a view privada pertence à capacidade do mm e não tem account_object.
Tipo/identidade não estabelecido conserva a classificação conservadora anterior.
Não se retirou uma syscall nem se tornou um programa Processavel falso.

Sucesso em truncate não exclusivo ainda exige observação de saída antes de
retomar userspace. stop_world coleta os exits pendentes antes do snapshot; o
resultado identifica o alvo e atualiza o adapter antes da reconciliação. EXIT
recupera o retorno real se SIGKILL suprimiu o processamento normal, antes de
exit_mm/exit_files. O teste dedicado usa syscall real commitada, SIGKILL real e
recuperação por registradores; o hook só existe no build de testes.

O caminho ordinário sem objeto não reconcilia indiscriminadamente eventos
pendentes de outros memfds enquanto conclui. Um alvo adaptado descoberto após
execução não exclusiva incrementa unsupported_object_events. Esse diagnóstico
não é detecção completa de troca de pathname: uma troca de volta ou truncate
do mesmo tamanho pode escapar. A consulta preflight não é atômica com a syscall.
Não se afirma que essa classificação seja um contrato completo para todo Linux.

## Janela inicial do serviço

O modo aditivo [--service-window](SERVICE_WINDOW.md) abre scope no observer
imediatamente após o primeiro baseline publicado (sequência 1), antes de setenv,
gate, metadata restante e fork/exec. O host adota a identidade existente por
window_read/barrier e fecha ao concluir init. Não se inicia o scope depois de
Python/compilação nem se reconstrói um prefixo com eventos inventados. O modo
genérico conserva NONE até begin explícito. As ABIs 120/280 não mudaram, não há
env novo/Nat/fuel ou fechamento automático. O contrato monotônico do bootstrap
estático pinado continua pendente de ratificação final e INCOMPLETE permanece.

## Alcance das entradas e obrigação de lease

[ENTRY_PROFILE_V6.md](ENTRY_PROFILE_V6.md) registra a análise causal de Popen,
Node SpawnSync/libuv, main BTT/Lean e flags Clang. Seus caminhos auditados têm
comandos de fd/locks constantes e não fornecem F_SETLEASE ao kernel. O input Bend
é programa puro/dado, não callback Python, JS ou Lean IO. Isso não depende da
ausência de uma syscall num trace e não acrescenta restrição à linguagem.

A conclusão é localizada e condicional: o callgraph de todas as dependências e
initializers, o perfil de ambiente, fd herdado/importado e os bytes finais ainda
exigem ratificação. O arquivo ENTRY_PROFILE_V6.json é uma leitura de 13 inputs
esses caminhos, não um novo CLOSURE final. ROOT continua alterando host/native.

O kernel shmem aceita generic_setlease. Um memfd read-only pode adquirir F_RDLCK
após fechar o writable; o novo fixture demonstra isso e conclui livre. Observado,
truncate do objeto conhecido ainda bloqueia o handler no slot exclusivo. As duas
execuções report/no-report e seu estado de espera estão em
[REVIEW_V5_RESULTS.json](../../tests/accounting/REVIEW_V5_RESULTS.json), campo
unresolved_obligations. **Esse progresso geral não está corrigido.** Não foi
marcado como teste de reparo aprovado nem ocultado por um guard. Não se alterou
lease-break-time. A integração deve provar exclusão causal dessa aquisição no
perfil real final ou fornecer solução de scheduler que preserve as barreiras de
backing; as leituras locais ainda não constituem essa prova completa.

Também continuam INCOMPLETE as mutações bloqueantes gerais, TOCTOU de
path/open_how/dirfd, namespaces/mounts/procfs, payload importado/especial/hugetlb,
efeitos parciais não auditados, bootstrap, ordenação syscall/EXIT pinada e
Sem_Ctx/CLI/init/framing/Campo/watchdog. A retenção/capacidade de views de arquivos
comuns conserva as regras existentes; os controles de serialização não provam
toda invalidação de mappings por truncate, page fault ou filesystem externo.
Não há afirmação MedicaoReal, Lei 2, Contrato ou cobertura completa das leis.

## Validação e freeze

```sh
python3 -B tests/accounting/test_accounting.py -v
python3 -B tools/accounting/replay_v5_review.py
```

Passaram **64/64 métodos**, incluindo os 52 anteriores literalmente preservados
no AST e doze novos. RESULTS.json contém 265 registros, hashes de fontes antes/
depois e do build. A rodada final está registrada no manifesto V6. Os novos casos
cobrem os dois originais três vezes com controle/report/no-report; self/thread-self,
symlink intermediário, fd >=180, controles de flags; symlink final memfd/FIFO;
thread real de TID distinto; objeto memfd e mappings compartilhado/privado;
quatro aberturas truncantes com lease; recuperação em EXIT; aquisição transitória
pré-main de 64 MiB; adoção do scope inicial em Python/helper; fechamento e novo
scope local sem herdar pico de startup; e CLI direto/Python, com/sem relatório.

O comparador causal conserva 60 execuções de expectativas locais sobre V3/V4/V5/
current, mais três execuções separadas da obrigação de lease adaptada. Os dois
repros originais falham nos controles V5 e concluem em current; V3 conclui ambos;
V4 conclui lease/truncate e conserva a falha FIFO. As quatro aberturas truncantes
com lease também bloqueiam V5 e concluem em current. A espera longa original de
47,208 s e o EAGAIN forçado estão preservados na revisão, sem repetir nem ampliar
esse relógio. Timeout de harness apenas limpa experimentos; não representa
FalhaReal, excesso ou K do banco.

O checkpoint V6 inclui apenas accounting e suas evidências; V3/V4/V5, manifestos,
sidecars, históricos 18/12/27/32/43/52 e capturas antigas ficam preservados. O
CLOSURE global continua provisório e fora do freeze. É necessária uma NOVA task
de revisão independente, criada por ROOT; esta implementação não executa essa
revisão nem delega trabalho.
