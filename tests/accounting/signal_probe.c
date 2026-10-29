#define _GNU_SOURCE
#include <assert.h>
#include <errno.h>
#include <inttypes.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/wait.h>
#include <unistd.h>

static uint64_t bits(const sigset_t *set) {
  uint64_t value=0;
  for(int signo=1;signo<NSIG;signo++)
    if(sigismember(set,signo)==1)value|=UINT64_C(1)<<(signo-1);
  return value;
}
int main(void) {
  struct sigaction action;sigset_t mask;
  assert(!sigaction(SIGCHLD,NULL,&action));
  assert(!sigprocmask(SIG_BLOCK,NULL,&mask));
  printf("{\"ignored\":%d,\"default\":%d,\"flags\":%u,\"action_mask\":\"%" PRIu64 "\",\"process_mask\":\"%" PRIu64 "\"}\n",
    action.sa_handler==SIG_IGN,action.sa_handler==SIG_DFL,
    (unsigned)action.sa_flags,bits(&action.sa_mask),bits(&mask));
  pid_t child=fork();assert(child>=0);if(!child)_exit(0);
  int status=0;pid_t result;do{result=waitpid(child,&status,0);}while(result<0&&errno==EINTR);
  printf("{\"wait_result\":%d,\"wait_errno\":%d}\n",result<0?-1:1,result<0?errno:0);
  return 0;
}
