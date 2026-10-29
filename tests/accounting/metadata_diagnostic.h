/* Explicit diagnostic build only. Real SIGKILL before a critical request;
 * record its actual errno. No mocked ptrace return or production hook. */
#ifndef JAYACCT_METADATA_DIAGNOSTIC_H
#define JAYACCT_METADATA_DIAGNOSTIC_H
#define _GNU_SOURCE
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <sys/ptrace.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/syscall.h>
#include <sys/user.h>
#include <unistd.h>
static int diag_event,diag_skip,diag_seen,diag_fired;
static pid_t diag_pid;
__attribute__((unused)) static pid_t diag_waitpid(pid_t pid,int*status,int options) {
  pid_t out=waitpid(pid,status,options);
  if(out>0&&WIFSTOPPED(*status)){diag_pid=out;diag_event=*status>>16;}
  return out;
}
__attribute__((unused)) static long diag_ptrace(enum __ptrace_request request,pid_t pid,void*address,void*data) {
  const char*kind=getenv("JAYACCT_DIAG_METADATA");
  int creation=diag_event==PTRACE_EVENT_CLONE||diag_event==PTRACE_EVENT_FORK||diag_event==PTRACE_EVENT_VFORK;
  struct user_regs_struct regs;int descriptor=0;
  if(kind&&!strcmp(kind,"descriptor")&&request==PTRACE_PEEKDATA&&
     !ptrace(PTRACE_GETREGS,pid,0,&regs)&&regs.orig_rax==SYS_io_uring_setup)descriptor=1;
  int match=kind&&pid==diag_pid&&
    ((!strcmp(kind,"clone")&&creation&&request==PTRACE_GETEVENTMSG)||
     (!strcmp(kind,"exec")&&diag_event==PTRACE_EVENT_EXEC&&request==PTRACE_GETEVENTMSG)||
     (!strcmp(kind,"flags")&&creation&&request==PTRACE_PEEKDATA)||
     (!strcmp(kind,"regs")&&diag_event==PTRACE_EVENT_EXIT&&request==PTRACE_GETREGS)||
     (!strcmp(kind,"descriptor")&&descriptor)||
     (!strcmp(kind,"regs_release")&&diag_event==PTRACE_EVENT_EXIT&&request==PTRACE_GETREGS));
  if(match&&!diag_fired){
    const char*skip=getenv("JAYACCT_DIAG_SKIP");diag_skip=skip?atoi(skip):1;
    if(diag_seen++==diag_skip){
      diag_fired=1;
      if(!strcmp(kind,"regs_release")) {
        /* Advance an actual EXIT stop to an unreaped terminal status. The
         * later GETREGS really fails; cached returns/other owners are real. */
        if(ptrace(PTRACE_CONT,pid,0,0))_exit(124);
        siginfo_t info={0};if(waitid(P_PID,(id_t)pid,&info,WEXITED|WNOWAIT|__WALL))_exit(124);
      } else if(kill(pid,SIGKILL))_exit(124);
    }
  }
  long out=ptrace(request,pid,address,data);int saved=errno;
  if(match&&diag_fired){char b[160];int n=snprintf(b,sizeof b,"DIAGNOSTIC metadata request %u pid %d result %ld errno %d event %d\n",request,pid,out,out<0?saved:0,diag_event);if(n>0)(void)write(2,b,(size_t)n);}
  errno=saved;return out;
}
#define waitpid diag_waitpid
#define ptrace(request,pid,address,data) diag_ptrace(request,pid,(void*)(uintptr_t)(address),(void*)(uintptr_t)(data))
#endif
