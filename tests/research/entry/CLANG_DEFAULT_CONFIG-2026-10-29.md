# Configuração implícita do compilador: controle isolado

O Clang 19 fixado foi exercitado com e sem `--no-default-config`. Não foi
alterado nenhum arquivo de sistema nem o candidato V8 do serviço. O controle
identifica uma opção concreta para fechar o perfil de ferramentas; não é um
novo defeito demonstrado na entrada instalada do banco.

O [manual da versão 19.1](https://releases.llvm.org/19.1.0/tools/clang/docs/UsersManual.html#configuration-files)
descreve configuração automática por nome do driver/triple e por diretórios
de busca, incluindo o diretório do executável. A opção
`--no-default-config` desativa essa busca automática.

No executável instalado, strace registrou tentativas em
`/usr/lib/llvm-19/bin/{x86_64-pc-linux-gnu-clang,clang,x86_64-pc-linux-gnu}.cfg`,
todas ENOENT. Um HOME privado não acrescentou busca de config neste build.
Não se concluiu que o usuário possa inserir uma dessas configurações na
entrada concreta, nem que essas condições possam ser dispensadas de sua
identidade e estabilidade.

Em `/tmp/jaydb2-clang-profile-1mq_dg_5`, uma cópia literal do mesmo ELF recebeu
um arquivo adjacente de fixture com `-DJAYDB_CONFIG_PROBE=42`. O fonte C
pré-processado usa zero quando a macro não foi definida:

| Execução | Saída | Status |
| --- | --- | --- |
| Executável instalado, sem config encontrada | `0` | 0 |
| Cópia do mesmo ELF, config automática adjacente | `42` | 0 |
| Mesma cópia/config com `--no-default-config` | `0` | 0 |

Ambos os ELFs têm SHA-256
`f6d5286a52de10b1e3e8841457c9903a1ea28f222ac0f58cd616697d0dcd9db3`.
As saídas, comandos e o trace estão no diretório do ensaio. O replay é
`/tmp/jaydb2-clang-profile-replay.py`; ele cria uma nova pasta e não modifica
o compilador instalado. O teste só faz pré-processamento, sem executar C,
carregar plugins ou compilar uma requisição do banco.

Os builders atuais ainda não foram alterados. Uma futura escolha explícita
dessa opção precisa integrar os comandos e suas identidades, ser validada
nos builds reais e passar pela revisão correspondente. Desativar config
automática não fixa sozinho headers, linker, bibliotecas, ELF inicializadores,
ambiente ou o fechamento completo das ferramentas. Não foi produzido
`MedicaoReal`, um limite público ou evidência de memória completa.
