#ifndef JAYACCT_SIGNAL_RESTORE_DIAGNOSTIC_H
#define JAYACCT_SIGNAL_RESTORE_DIAGNOSTIC_H
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <errno.h>
#include <signal.h>
#include <stdio.h>
#include <sys/syscall.h>
#include <unistd.h>

/* Explicit separate diagnostic ELF only. The negative result is a real Linux
 * rt_sigaction EFAULT, not a fabricated errno or a production test hook. */
static pid_t signal_install_pid;
static int __attribute__((unused)) signal_diagnostic_action(int signo,
    const struct sigaction *action,struct sigaction *previous) {
  if(signo==SIGCHLD&&action&&previous)signal_install_pid=getpid();
  if(signo==SIGCHLD&&action&&!previous&&signal_install_pid&&getpid()!=signal_install_pid) {
    long result=syscall(SYS_rt_sigaction,SIGCHLD,(void *)1,NULL,8);
    int error=errno;
    dprintf(STDERR_FILENO,"diagnostic child restore raw_result=%ld errno=%d\n",result,error);
    errno=error;return (int)result;
  }
  return sigaction(signo,action,previous);
}
#define sigaction(signo,action,previous) signal_diagnostic_action(signo,action,previous)
#endif
