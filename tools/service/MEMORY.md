> Histórico anterior à retirada autorizada dos orçamentos físicos. Este mecanismo não integra o serviço ativo; veja `../../PROPOSTA_RECURSOS_SIMPLES.md` e `../../native/SIMPLE_RUNTIME.md`. O texto e os resultados abaixo pertencem ao escopo anterior.

# Memória física: resultado da investigação

**Decisão posterior do usuário (2026-10-28):** a medida pública será bytes
efetivamente alocados pelo serviço, incluindo núcleo, verificador e compilação.
O relatório abaixo conserva a investigação anterior sobre páginas residentes;
RSS e cgroup não serão usados como substitutos da medida escolhida. A
contabilização síncrona de backing ativo está em implementação. A soma
amostrada de RSS foi removida do controlador: ela não pode justificar o erro
público `limite` segundo a medida escolhida.

O adaptador `memory.py::MemoryWindow` lê o pico local de um escopo exato do
contador, confere flags e proveniência e só produz `MemoryExcess` com excesso
estrito e cobertura completa. Ele recusa `INCOMPLETE`, inclusive quando o
número observado está acima do teto. O helper aceita esse monitor privado e
conserva a origem de um excesso transitório anterior à sua saída; mata e
recolhe seus filhos quando a monitoração interrompe a execução.

A abertura da janela para todo o cenário e sua conexão ao controlador ainda
estão pendentes. O caminho experimental sem uma janela não fabrica uma medida
substituta. Essa leitura de histórico também não autoriza construir Campo:
isso exige a barreira C síncrona, stack ativa e stores protegidos descritos em
`native/FIELD.md`. A nova fronteira de conclusão prepara o erro fixo antes da
decisão e pode selecioná-lo em C sem publicar o candidato; ver `COMMIT.md`.

**Escopo esclarecido pelo usuário (2026-10-28):** contar os processos do serviço
e excluir memória interna do kernel, inclusive temporários de syscalls não
entregues aos processos. Isso inclui backing retido por fd quando sua capacidade
foi adquirida pelo userspace, além dos mappings; padding ou estruturas internas
do kernel não entregues ficam fora. A decisão não certifica automaticamente a
cobertura do observador, a janela de Campo nem a medida do executável completo.

Investigação local de 2026-10-28. **Não foi encontrado um mecanismo neste host
que, acrescentado apenas ao controlador como monitor, demonstre simultaneamente
as obrigações de memória das oito leis.** Não foi implementada uma API chamada
`MedicaoReal` para RSS amostrado, capacidade de arena ou contabilidade de cgroup.
Este documento é a entrega técnica alternativa solicitada, com contraexemplos,
experimentos executados e código para reproduzi-los.

Há um resultado operacional positivo: `systemd-run --user` consegue criar uma
unidade transitória isolada com `MemoryMax`. Há também dois resultados negativos
concretos: OOM ocorreu sem `memory.peak > memory.max`, e um mapeamento com 16 MiB
residentes não foi cobrado como `file` no cgroup que o usava. Portanto, habilitar
essa facilidade não resolve a ligação exigida pelo contrato.

Nenhum teto do banco, fragmento, contrato, serviço existente ou parâmetro global
foi modificado. Os tetos menores abaixo pertencem exclusivamente aos probes.
`controller.py`, `abi.py`, `staging.py`, o núcleo e `native/` não foram editados.

## 1. Obrigações que o mecanismo teria de satisfazer

Sejam `B = X.limite(c, X.Memoria{})` e `M(t)` a memória física real do artefato
completo, conforme o ambiente fixado, incluindo Python, helpers, DSOs, TLS,
loader, libc, stacks e buffers. O escopo não pode ser reduzido ao heap Bend.
O contrato ainda exige a ligação entre fatos e ambiente; não permite escolher
uma interpretação conveniente de `M` pela implementação.

As condições relevantes são distintas:

1. Em **cada** fato real `I.AlocouCampo{pos,n,memoria_depois}` no instante `t`,
   deve haver `ConferiuComprimento{pos,n}` anterior e `memoria_depois <= B`
   (`LAWS.Regra2`). A memória desse evento precisa corresponder à memória real.
2. Para justificar `limite` por memória, precisa existir `u < t_conclusao` e uma
   quantidade efetivamente medida `n > B`, com `I.Mediu{Memoria,n}` e
   `I.MedicaoReal(...)` (`Interface.RespostaJustificada`, `LAWS.Regra7`).
   Igualdade não basta. A prova `proof/Recursos.bend` recebe essas hipóteses;
   ela não constrói a medição do SO.
3. `Processavel(a,x)` é uma condição externa, independente do artefato candidato
   (`Interface.bend`). Não pode ser tornada falsa pela própria política de
   alocação, demora ou recusa. A Lei 8 continua exigindo progresso quando essa
   condição é verdadeira. Um bloqueio do mecanismo não se torna automaticamente
   uma falha ambiental real.

**Não há aqui uma demonstração de inconsistência das leis.** A Lei 2 não afirma
`M(t) <= B` em todo instante: seu teste de memória é específico a
`AlocouCampo`. Um excesso real causado por outra atividade pode fornecer a
testemunha para `limite`, desde que nenhum evento de campo já tenha violado a
Lei 2. Também pode existir uma falha ambiental real sem excesso. O problema é
demonstrar esses fatos, com sua ordem correta, no runtime concreto.

## 2. Por que um amostrador externo não basta

Considere um campo cuja alocação física termine no instante `a`, entre duas
leituras do monitor `s0 < a < s1`. Se `M(s0) <= B` e `M(a) > B`, o fato
`AlocouCampo` já viola a Lei 2. Detectar o excesso em `s1` e matar o processo
fornece, no máximo, uma possível justificativa posterior de `limite`; não
corrige o evento anterior. Reduzir o intervalo de polling não elimina essa
execução, pois não cria uma relação de sincronização com o evento.

Se a alocação e a liberação ocorrerem entre leituras, o excesso também pode não
ser observado. Picos por processo não fornecem o instante nem o pico conjunto.

Há um segundo defeito independente na soma sequencial de processos. Para dois
processos A e B, em MiB, uma execução pode ter:

```text
instante da leitura de A: A=40, B=4
transição:               A libera 36; depois B aloca 36
instante da leitura de B: A=4,  B=40
```

O total real nunca passou de 44 MiB, mas a soma das leituras é 80 MiB. Para um
teto de 60 MiB, a soma acusaria excesso inexistente. Logo,
`sum(RSS_i(t_i)) > B` não implica `exists t: sum(RSS_i(t)) > B`, mesmo supondo
cada leitura individual exata e ignorando compartilhamento.

`controller.resident_group` tem precisamente essa forma de varredura e usa
`/proc/PID/stat`. O kernel também documenta atualização assíncrona dos contadores
RSS; `smaps` melhora a observação individual, sem produzir uma transação entre
processos. [Documentação de /proc](https://www.kernel.org/doc/html/latest/filesystems/proc.html).

Se a memória física significa páginas residentes distintas, há ainda duplicação:
no probe local, dois aliases do mesmo memfd de 16 MiB apresentaram **16 MiB de
RSS cada**, totalizando 32 MiB para os mesmos 16 MiB de conteúdo físico. PSS de
cada alias foi 8 MiB. PSS tampouco identifica automaticamente o conjunto físico
do serviço quando há compartilhamento com processos externos.

Esses contraexemplos têm consequências de segurança e progresso: o amostrador
pode deixar passar um evento inválido e pode recusar por um excesso inexistente.
Portanto a exceção `StageMemory` do helper atual ainda não constitui, por si,
evidência da `MedicaoReal` física exigida. Trocar `stat` por `smaps_rollup`, somar
`ru_maxrss` ou anexar um timestamp ao resultado não resolve essas duas questões.

## 3. O que o backend atual realmente contabiliza

Em `native/module_tail.c`, `jaydb_run` começa com a imagem DSO e soma capacidades
de input, output, stack de Terms, stack nativa e páginas de guarda. O heap recebe
o restante arredondado para baixo. Quando a arena é criada:

```text
charged_bytes = fixed + heap_size <= request.memory_bytes
```

Uma capacidade incompatível ou um crescimento além da arena resulta em
`JAYDB_MEMORY`. Não há nesse caminho uma medição de `M` estritamente superior ao
teto. Reservas `mmap` não demonstram residência e páginas de guarda nem sequer
têm a mesma natureza de páginas de dados residentes. As omissões de host,
bookkeeping, TLS e bibliotecas estão reconhecidas em `native/README.md`.

Além disso, `Module.run` aloca cópias ctypes de input/output **antes** de entrar
na guarda nativa; `dlopen` ocorre na construção de `Module`; o framing e o
empacotamento Python alocam fora dessa guarda. Um contador acrescentado somente
ao callback C não passa a cobrir esses caminhos nem os processos Node/Clang.

O mapeamento conservador de `JAYDB_MEMORY` para `falha` evita inventar
`Mediu{Memoria,B+1}`. Ele **não demonstra** que toda exaustão de capacidade interna
é `FalhaReal` ambiental, nem que o servidor completo já cumpre a Lei 8. O
bloqueio permanece explícito. É necessário corrigir a ligação, e não apenas
trocar o nome do status.

## 4. systemd/cgroup: disponível, mas não equivale ao contrato

O host desta execução apresentou Linux `7.0.0-38-generic`, systemd 255,
UID 1000 e montagem cgroup2 **rw**. Isso difere da informação anterior de
montagem readonly. O processo estava num scope de agentes de T3 Code sob
`user@1000.service`; o user manager respondeu normalmente.

Este comando executou com sucesso, sem alterar uma unidade existente:

```sh
systemd-run --user --quiet --wait --pipe --collect \
  --unit=jaydb-memory-probe-initial \
  --property=MemoryAccounting=yes --property=MemoryMax=67108864 \
  /bin/sh -c 'cat /proc/self/cgroup'
```

O processo apareceu em
`/user.slice/user-1000.slice/user@1000.service/app.slice/jaydb-memory-probe-initial.service`.
Novas unidades de teste usaram UUID e foram recolhidas ao terminar.
`MemoryMax` configura `memory.max`.
[Manual do systemd 255](https://www.freedesktop.org/software/systemd/man/255/systemd.resource-control.html).

### 4.1. OOM não fornece o número estritamente maior

Um supervisor Python pequeno criou um filho que tentou materializar 128 MiB
numa unidade com `MemoryMax=64 MiB`, `MemorySwapMax=0`, `OOMPolicy=continue`.
A unidade e o supervisor terminaram normalmente; o filho recebeu SIGKILL.
Valores realmente lidos após esse término:

```text
child_returncode = -9
memory.max       = 67108864
memory.peak      = 67108864
memory.current   = 6623232
memory.events: max=44, oom=1, oom_kill=1
```

Não há nessa evidência `n > 67108864`. Isso refuta a regra
`oom_kill > 0 => pode registrar Mediu{Memoria,B+1}`. Não afirma que todo OOM
terá o mesmo pico nem que um contador do kernel seja prova de ausência de
qualquer excesso físico interno.

O kernel distingue tentativa de ultrapassagem (`max`), OOM e medição; também
admite excessos temporários de `memory.max`. Assim, o teto não fornece nem a
testemunha estrita necessária, nem uma invariância exata por evento.
[Interface de memória do cgroup v2](https://www.kernel.org/doc/html/latest/admin-guide/cgroup-v2.html#memory-interface-files).

### 4.2. Contabilidade de cgroup não é a residência completa do serviço

No segundo experimento, o processo pai materializou um arquivo de 16 MiB e
manteve o mapeamento. Um novo serviço mapeou o mesmo arquivo e acessou todas as
páginas, mantendo o mapeamento vivo durante as leituras:

```text
smaps do mapeamento do serviço: Rss=16384 kB, Pss=8192 kB
memory.current do serviço:      5767168 bytes
memory.stat file:               0
memory.stat shmem:              0
```

Portanto nem mesmo os 16 MiB residentes desse mapeamento estavam incluídos na
cobrança total de aproximadamente 5,5 MiB da unidade. O mesmo problema de origem
da cobrança é relevante para bibliotecas compartilhadas já carregadas fora do
serviço. Não se corrige somando arbitrariamente todos os DSOs por tamanho ELF.

O kernel mantém a cobrança na origem, inclusive em migrações, e a contabilidade
também inclui page cache e memória de kernel. Logo não há equivalência geral
entre cobrança de cgroup e memória residente do artefato completo.
[Memory Ownership](https://www.kernel.org/doc/html/latest/admin-guide/cgroup-v2.html#memory-ownership).

Uma hierarquia própria iniciada **antes** do host Python e de todos os helpers
melhora o escopo; não transforma essa contabilidade na medida externa exigida.
Migrar o host atual depois de carregar dependências não recupera retroativamente
as cobranças. Matar só o filho também não interrompe uma alocação que aconteça
no host. Matar o host junto perde o estado e o canal que ele conserva: a
preservação/publicação e a resposta precisariam de uma arquitetura correspondente.

Um supervisor separado não pode ser excluído da memória do serviço só para
fazer a conta caber. Seu papel e sua memória precisam fazer parte da ligação
real do ambiente, assim como os do host atual.

## 5. RLIMIT_AS, permissões e alternativas locais

O Node 24.19.0 executou um programa curto e reportou:

```text
process.memoryUsage().rss = 43057152 bytes
/proc/self/status VmSize  = 1274820 kB
/proc/self/status VmRSS   = 42384 kB
```

As leituras ocorreram em instantes distintos; não se afirma igualdade entre os
dois valores de RSS. Ambos são muito inferiores à reserva virtual. Um teste
separado com `RLIMIT_AS=128 MiB` não terminou em 15 s e foi encerrado pelo
harness; **isso não foi classificado como excesso físico**.

Clang 19.1.1 sem esse rlimit conferiu `int main(void) { return 0; }`, com retorno
zero e pico `ru_maxrss=80916 KiB` no experimento isolado. Com `RLIMIT_AS=128 MiB`,
nem `clang-19 --version` carregou:

```text
returncode = 127
error while loading shared libraries: libLLVM.so.19.1:
failed to map segment from shared object
```

Logo o rlimit de VM pode bloquear antes do consumo físico configurado.
`tools/native/build.py` ainda o aplica a cada Clang. A alteração desse caminho é
do responsável pelo backend; este relatório não o modificou. Não se deve
resolver a falha aumentando o teto físico contratual nem chamando a reserva
virtual de consumo físico.

Uma página privada tocada no probe apresentou `present=True`, `PFN=0`, com
`CapEff=0`. `/proc/kpagecount` e `/proc/kpageflags` pertenciam a root com modo
0400. A interface pagemap oculta PFNs sem `CAP_SYS_ADMIN`.
[Documentação de pagemap](https://www.kernel.org/doc/html/latest/admin-guide/mm/pagemap.html).
Portanto não se dispõe aqui de enumeração não privilegiada e completa para
deduplicar por frame físico. Mesmo obter PFNs não daria uma fotografia atômica
de todos os eventos de alocação.

Também foram apenas lidos `perf_event_paranoid=4`,
`unprivileged_bpf_disabled=2`, `vm.unprivileged_userfaultfd=0` e o dispositivo
`/dev/userfaultfd` root 0600. Nenhum foi alterado. Não se infere daí que toda
modalidade de userfaultfd seja impossível. Registrar faltas em regiões
selecionadas, interceptar syscalls ou interpor `malloc` não cobre, por si só,
subalocações em páginas já residentes, todos os allocators e todos os efeitos
de loader/TLS/helpers.

## 6. Reprodutor dos três resultados centrais

Execute o Python abaixo como o usuário normal. Usa somente biblioteca padrão,
`/proc` e novas unidades transitórias. Cada serviço tem prazo de 15 s, o cliente
tem timeout de 20 s e o `finally` tenta parar **somente** o UUID criado. Não
modifica configuração global. O probe OOM tenta materializar no máximo 128 MiB,
dentro da unidade de 64 MiB. Os outros probes usam objetos de 16 MiB.

As asserções verificam as observações específicas, não as leis do banco. O pico
do probe OOM pode variar entre execuções: o programa imprime se houve testemunha
estrita no contador, sem pressupor que ela sempre exista.

```python
import json
import mmap
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import uuid

CAP = 64 * 1024**2
SIZE = 16 * 1024**2

COMMON = '''
import json, mmap, subprocess, sys
from pathlib import Path
relative = Path('/proc/self/cgroup').read_text().split('0::')[1].strip()
cg = Path('/sys/fs/cgroup') / relative.lstrip('/')
def pairs(name):
    return dict((k, int(v)) for k, v in
                (line.split() for line in (cg / name).read_text().splitlines()))
def counters():
    return {name: int((cg / name).read_text()) for name in
            ('memory.current', 'memory.peak', 'memory.max')}
def mapping_stats(name):
    result, current = [], None
    for line in Path('/proc/self/smaps').read_text().splitlines():
        if '-' in line.split()[0]:
            current = {} if name in line else None
            if current is not None:
                result.append(current)
        elif current is not None and line.split(':')[0] in ('Rss', 'Pss'):
            key, value = line.split(':')
            current[key] = int(value.split()[0]) * 1024
    return result
'''

def service(directory, code, *args):
    script = directory / (uuid.uuid4().hex + '.py')
    script.write_text(COMMON + code)
    unit = 'jaydb-memory-research-' + uuid.uuid4().hex + '.service'
    command = [
        'systemd-run', '--user', '--quiet', '--wait', '--pipe', '--collect',
        '--unit=' + unit, '--property=MemoryAccounting=yes',
        '--property=MemoryMax=' + str(CAP), '--property=MemorySwapMax=0',
        '--property=OOMPolicy=continue', '--property=RuntimeMaxSec=15s',
        '/usr/bin/python3', str(script), *map(str, args),
    ]
    try:
        p = subprocess.run(command, capture_output=True, text=True, timeout=20)
        assert p.returncode == 0, (p.returncode, p.stderr, p.stdout)
        return json.loads(p.stdout)
    finally:
        subprocess.run(['systemctl', '--user', 'stop', unit],
                       capture_output=True, timeout=5)

with tempfile.TemporaryDirectory(prefix='jaydb-memory-research-') as temporary:
    directory = Path(temporary)
    oom = service(directory, '''
p = subprocess.run([sys.executable, '-c',
    "import mmap; m=mmap.mmap(-1,128*1024**2); "
    "m[::4096]=b'x'*(128*1024**2//4096)"], capture_output=True)
print(json.dumps(dict(child_returncode=p.returncode,
                      counters=counters(), events=pairs('memory.events'))))
''')
    assert oom['child_returncode'] == -signal.SIGKILL, oom
    assert oom['events']['oom_kill'] >= 1, oom
    oom['counter_has_strict_witness'] = oom['counters']['memory.peak'] > CAP
    print('oom', json.dumps(oom))

    shared_file = directory / 'shared.bin'
    with shared_file.open('w+b') as f:
        f.truncate(SIZE)
        with mmap.mmap(f.fileno(), SIZE) as parent_mapping:
            parent_mapping[::4096] = b'x' * (SIZE // 4096)
            shared = service(directory, '''
with open(sys.argv[1], 'r+b') as f:
    with mmap.mmap(f.fileno(), 0) as m:
        for i in range(0, len(m), 4096):
            byte = m[i]
        print(json.dumps(dict(mapping=mapping_stats(sys.argv[1]),
                              counters=counters(), stats=pairs('memory.stat'))))
''', shared_file)
            assert shared['mapping'][0]['Rss'] == SIZE, shared
            assert shared['stats']['file'] < SIZE, shared
            print('externally_charged_mapping', json.dumps(shared))

    alias_name = 'jaydb-memory-alias-' + uuid.uuid4().hex
    fd = os.memfd_create(alias_name)
    try:
        os.ftruncate(fd, SIZE)
        with mmap.mmap(fd, SIZE) as a, mmap.mmap(fd, SIZE) as b:
            a[::4096] = b'x' * (SIZE // 4096)
            for i in range(0, SIZE, 4096):
                byte = b[i]
            # The same parser is used locally without executing COMMON's
            # cgroup setup or opening any other process's pagemap.
            namespace = {}
            exec(COMMON, namespace)
            aliases = namespace['mapping_stats'](alias_name)
            assert len(aliases) == 2, aliases
            assert sum(v['Rss'] for v in aliases) == 2 * SIZE, aliases
            print('aliases', json.dumps(aliases))
    finally:
        os.close(fd)
```

## 7. Caminho de implementação restante, preservando as leis

O caminho necessário é uma ligação de runtime, e não uma troca da função que
consulta `/proc`. Deve fornecer, conjuntamente:

1. **Escopo e medição correspondentes ao ambiente fixo.** Enumerar os componentes
   reais do serviço desde o bootstrap, incluindo compartilhamento e memória do
   mecanismo de controle. Não subtrair uma base escolhida, adicionar uma margem
   ao teto nem substituir a medida por capacidade/VM/cgroup. Se a política de
   compartilhamento ainda não está definida pelo ambiente externo, essa é uma
   obrigação semântica pendente, não liberdade para a implementação escolher.
2. **Uma relação síncrona com cada `AlocouCampo`.** Demonstrar a condição de memória
   naquele evento, cobrindo também crescimento concorrente do host e helpers.
   Não basta medir antes e permitir que outro componente cresça entre a leitura
   e o evento. Uma alocação real de campo não pode ser escondida como
   “tentativa” para emitir o fato somente quando o pós-teste aprovar.
3. **Uma causa real para cada aborto.** Se houver medição estritamente maior,
   registrar a testemunha anterior à conclusão. Caso a reserva só falhe
   preventivamente, isso não cria uma testemunha de memória. Se houve falha
   ambiental genuína, preservar sua identidade sem converter qualquer guard
   interno em `FalhaReal`. Prefaulting deliberado de memória desnecessária para
   fabricar excesso também não resolve o progresso externo.
4. **Interrupção compatível com estado e protocolo.** Suspender novas operações,
   descartar o trabalho privado e conservar o estado publicado. Controle por
   processo precisa demonstrar também o papel do supervisor/host e a entrega
   possível da resposta; o kill de um cgroup não é essa demonstração.

Uma reserva fixa pode ajudar a provar que determinados eventos cabem, mas isso
requer que **todos** os custos físicos relevantes estejam efetivamente cobertos
e que o mecanismo não introduza recusas arbitrárias de casos processáveis. Não
se deduz que toda implementação com reservas seja impossível. Também não se
deduz a possibilidade de um runtime geral exato a partir desses probes.

Não foi produzido um `metrics.py` de produção porque as primitivas testadas
não fornecem os itens 1–4. Uma função que retornasse um número com o nome
`memoria_real` esconderia justamente a obrigação que falta. Os experimentos
demonstram uma contenção utilizável como defesa operacional e refutam sua
promoção automática a prova do contrato. A mudança seguinte precisa ocorrer
na arquitetura/ligação do ambiente e nos pontos reais de alocação, que pertencem
às outras frentes de trabalho, mantendo esse bloqueio aberto até haver prova
ou mecanismo correspondente.

Não é necessária uma escolha do usuário entre RSS e cgroup para concluir esta
investigação: ambos foram demonstrados insuficientes para a integração atual.
Com as leis e o escopo físico preservados, autorizar mais polling ou habilitar
`MemoryMax` não preencheria a lacuna. Este relatório não solicita relaxamento
do contrato nem declara impossibilidade de qualquer implementação futura.

## 8. Validação da entrega

O bloco Python da seção 6 foi extraído deste arquivo e executado integralmente,
com retorno zero. Reproduziu `memory.peak == memory.max == 67108864` com OOM,
`file=0` diante de um mapeamento residente de 16777216 bytes e dois aliases com
16777216 bytes de RSS cada. As asserções passaram. Uma consulta posterior não
encontrou unidades `jaydb-memory-research-*` ou `jaydb-memory-probe-*` restantes.

`python3 -m unittest discover -s tests/service -p 'test_controller.py' -v`
também passou os seis testes existentes. Esses testes de transporte não
demonstram as obrigações de memória; registram apenas a verificação executada.
