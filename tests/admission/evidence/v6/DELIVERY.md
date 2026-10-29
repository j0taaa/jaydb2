# Entrega V6 — candidato funcional congelado

O gate real integra R4 e a extensão estrutural de R5. Fontes, testes, pins e caches estão estáveis. A revisão independente nova pertence ao ROOT e continua pendente. Esta entrega não declara generalidade total nem preservação semântica completa do frontend.

- Snapshot: `tests/admission/checkpoints/resources_v6.tar.gz`, SHA256 `0e1681cb261ca6ffe5988b7d6712e7323ad41c405693340dc510213eb76e7956`.
- Manifesto e inventário de todos os 174 arquivos do snapshot: `tests/admission/checkpoints/resources_v6.json`.
- Pin do frontend: `088998b49d373d87cf0529b39408fe3bbfb4c7121e2ef7b79af5d8a83400fe3a`.
- Grupo para commit pelo ROOT: `tests/admission/evidence/v6/commit-ready.json`. A comparação usa o archive V5, sem consultar ou modificar Git. O manifesto de commit exclui a atualização de `contract.lock.json`, que pertence ao ROOT, mas registra seu hash como dependência.

## Evidência concluída

Suíte proporcional completa: 165/165 PASS, zero falhas, 780.53 s. Jitless: seis verificações distintas concluídas com sucesso, incluindo R4/R5, matriz causal de corpos/dependências/aliases/Base, Token recursivo e o certificado que usa o helper R5. O primeiro pacote jitless estava sem Base oficial e seus dois erros de embalagem estão preservados; apenas esses dois foram repetidos após a cópia fixada. Nenhum resultado incompleto foi contado como PASS.

O próprio snapshot foi extraído em `/tmp/jaydb2-resources-v6-final-extracted`. A recompilação reproduziu os cinco JS e o binário/manifesto/C do verificador; os casos API R4/R5 nessa extração passaram 2/2. Logs e hashes estão em `after-snapshot/`. O addon stack preservado de V5 contém caminho absoluto em metadados `__FILE__`: seu rebuild em outro diretório difere, portanto foi restaurado o binário original autenticado antes dos testes API. Não se afirma rebuild byte-idêntico desse addon.

O payload real de `Bindings.certificado`, SHA256 `9a25da0c672e7a4e0ea9e1efa4a16e3bbfa8d0aa03008a95dcac5444982eccc9`, contém o alvo original e o vínculo do valor exato da evidência de `Client.theorem(n)`. Ambos os kernels aceitam; o C do mesmo Book retorna `Dados.VInt{0, 6}`. Alterar a dependência física realmente alcançada `Client:f~0` para Nat2 é recusado por ambos em `Client.f_7e_0.source_link`. O checker não apaga essa alteração. Artefatos e reprodutor estão em `certificate/` e `capture-certificate.mjs`.

Originais históricos 18, contrato ativo 14, cinco fontes oficiais, kernel original, generic4b71ed, V1–V5 e os 67 arquivos históricos foram conferidos. Os 67 arquivos e seu manifesto também estão preservados em `research-checkpoint.tar.gz`. As mudanças concorrentes do serviço pertencem ao ROOT; esta entrega não lhes atribui um hash antigo nem valida o novo reparo reentrante.

## Fontes e interface

Alteradas: `tools/admission/{bootstrap,build-frontend,closed-instances,frontend-cache,index,instance-keys,safe-templates}.mjs`, documentação de `run.py`, `tools/verifier/check.mjs`, testes e documentação próprios. Os 18 módulos planos novos são `structural-{syntax,relations,types,bodies,data,identity,boundary,entry,evidence,reflection,emitter,views,position,order}.mjs`, `template-affected.mjs` e `safe-{canonical,state,routing}.mjs`. O inventário com hashes é a autoridade para commit; o snapshot inclui o binário e manifesto instalados do verificador sem alterar seu pin.

APIs públicas mantidas. `options.verification` permanece opcional; não há campo físico obrigatório reintroduzido. `report.verifier.correspondence` identifica rota, alvos originais, obrigações e identidade justificada. O mesmo Book conserva corpos físicos, alvos e links independentes; não há definição nova após checker final nem fallback após falha lógica de guard/kernel.

Limitações explícitas: grupos de avaliadores vivos mutuamente recursivos gerados, reflexão de entradas opacas abstratas/de prova, renderizações apagadas ainda não implementadas e Stringmax. Formas sem representação estabelecida não ganham axioma ou hipótese `R_h` externa para uma entrada fechada. O marco funcional permanece sujeito à revisão matemática independente.

Nenhum comando git/gh, commit, push, delegação ou revisão própria foi executado por este worker.
