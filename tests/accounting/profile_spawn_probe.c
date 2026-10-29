#define _GNU_SOURCE
#include "deadline.h"
#include "profile_service3/lifecycle.h"
#include <assert.h>
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>
static void stage(const char*n) {
  struct jayacct_snapshot s={0};assert(!jayacct_barrier(&s));
  printf("STAGE %s %llu %llu %llu\n",n,(unsigned long long)s.sequence.lo,
    (unsigned long long)s.current.lo,(unsigned long long)s.flags);
}
static int helper(int bad,int inherited) {
  assert(getsid(0)==getpid()&&getpgrp()==getpid());
  assert(getenv("BEND_NO_TELEMETRY")&&!strcmp(getenv("BEND_NO_TELEMETRY"),"1"));
  errno=0;assert(fcntl(inherited,F_GETFD)==-1&&errno==EBADF);
  int gate[2];assert(!pipe(gate));pid_t child=fork();assert(child>=0);
  if(!child) {
    assert(!close(gate[0]));dprintf(1,"DESC %d\n",getpid());
    assert(!close(1)&&!close(2));assert(write(gate[1],"r",1)==1);for(;;)pause();
  }
  char b;assert(read(gate[0],&b,1)==1);return bad;
}
int main(int argc,char**argv) {
  if(argc==4&&!strcmp(argv[1],"helper"))return helper(atoi(argv[2]),atoi(argv[3]));
  assert(argc==3);setbuf(stdout,NULL);assert(!prctl(PR_SET_CHILD_SUBREAPER,1));
  struct rlimit core;assert(!getrlimit(RLIMIT_CORE,&core));rlim_t hard=core.rlim_max;
  core.rlim_cur=0;assert(!setrlimit(RLIMIT_CORE,&core));
  stage("baseline");void*library=dlopen(argv[1],RTLD_NOW|RTLD_LOCAL|RTLD_NODELETE);assert(library);
  const jaydb_lifecycle_descriptor_v1*(*describe)(void)=dlsym(library,"jaydb_lifecycle_describe_v1");
  int(*prepare)(jaydb_lifecycle_process_v1*)=dlsym(library,"jaydb_lifecycle_process_prepare_v1");
  int(*start)(jaydb_lifecycle_process_v1*,char*const[],char*const[])=dlsym(library,"jaydb_lifecycle_process_start_v1");
  int(*poll)(jaydb_lifecycle_process_v1*)=dlsym(library,"jaydb_lifecycle_process_poll_v1");
  int(*stop)(jaydb_lifecycle_process_v1*)=dlsym(library,"jaydb_lifecycle_process_stop_v1");
  int(*close_owner)(jaydb_lifecycle_process_v1*)=dlsym(library,"jaydb_lifecycle_process_close_v1");
  assert(describe&&prepare&&start&&poll&&stop&&close_owner&&describe()->flags==15);
  stage("nodelete_loaded");
  int inherited=open("/dev/null",O_RDONLY);assert(inherited>=3);
  jaydb_lifecycle_process_v1 p={.abi=1,.size=sizeof p,.prepare={.abi=1},
    .spawn={.receipt={.abi=1}},.finish={.receipt={.abi=1}},.fds={-1,-1,-1,-1}};
  assert(!prepare(&p));char fd[24];snprintf(fd,sizeof fd,"%d",inherited);
  char*args[]={argv[0],"helper",argv[2],fd,NULL};
  char*env[]={"BEND_NO_TELEMETRY=1","PATH=/usr/bin:/bin",NULL};assert(!start(&p,args,env));
  assert(p.spawn.pid>0&&atomic_load(&p.spawn.receipt.outcome)==1);
  char output[128]={0};size_t used=0;
  while(!(atomic_load(&p.flags)&JAYLC_EXIT_OBSERVED)) {
    assert(!poll(&p));ssize_t n=read(p.fds[0],output+used,sizeof output-1-used);
    if(n>0)used+=(size_t)n;else assert(!n||errno==EAGAIN||errno==EINTR);
  }
  while(used<sizeof output-1){ssize_t n=read(p.fds[0],output+used,sizeof output-1-used);if(n>0)used+=(size_t)n;else break;}
  pid_t descendant=0;assert(sscanf(output,"DESC %d",&descendant)==1&&descendant>0);
  siginfo_t info={0};assert(!waitid(P_PID,(id_t)p.spawn.pid,&info,WEXITED|WNOWAIT|WNOHANG));
  assert(info.si_pid==p.spawn.pid&&info.si_code==CLD_EXITED&&info.si_status==atoi(argv[2]));
  assert(!kill(-p.spawn.pid,0));stage("leader_unreaped_descendant_alive");
  assert(!stop(&p)&&!close_owner(&p));int status;
  assert(waitpid(descendant,&status,0)==descendant&&WIFSIGNALED(status)&&WTERMSIG(status)==SIGKILL);
  assert(!close(inherited));stage("group_reaped");assert(!dlclose(library));
  assert(describe()->flags==15);stage("nodelete_retained");
  assert(!getrlimit(RLIMIT_CORE,&core)&&core.rlim_max==hard&&core.rlim_cur==0);
  struct jayacct_window_snapshot w;assert(!jayacct_window_barrier(&w));
  assert(w.state==JAYACCT_WINDOW_ACTIVE&&w.scope_id.lo==1&&w.begin_sequence.lo==1);
  assert(!jayacct_window_end(&w));
  puts("FACT source_service3_spawn_setsid_closefrom_WNOWAIT_kill_reap_NODELETE 1");return 0;
}
