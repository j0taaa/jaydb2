#define _GNU_SOURCE
#include <assert.h>
#include <signal.h>
#include <stdlib.h>
#include <unistd.h>

static void caught(int signo) {(void)signo;}

/* A real exec launcher, with no Python startup between setup and exec. */
int main(int argc,char **argv) {
  assert(argc>=5);
  int mode=atoi(argv[1]),mask=atoi(argv[2]);
  struct sigaction action={0};
  action.sa_handler=mode==1?SIG_IGN:mode==2?caught:SIG_DFL;
  action.sa_flags=SA_RESTART|SA_NOCLDSTOP|SA_NOCLDWAIT;
  assert(!sigemptyset(&action.sa_mask));
  assert(!sigaddset(&action.sa_mask,SIGUSR2));
  assert(!sigaction(SIGCHLD,&action,NULL));
  sigset_t blocked;assert(!sigemptyset(&blocked));
  if(mask&1)assert(!sigaddset(&blocked,SIGCHLD));
  if(mask&2)assert(!sigaddset(&blocked,SIGUSR1));
  assert(!sigprocmask(SIG_SETMASK,&blocked,NULL));
  execvp(argv[3],argv+3);
  _exit(127);
}
