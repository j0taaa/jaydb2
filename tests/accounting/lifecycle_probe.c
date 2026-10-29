#define _GNU_SOURCE
#include "counter.h"
#include <assert.h>
#include <pthread.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>
static char *executable;
static char expected_pid[32];
static pthread_barrier_t ready;
static void observation(void) { struct jayacct_snapshot n;assert(!jayacct_barrier(&n)); }
static void *exec_thread(void*unused) {
  (void)unused;pthread_barrier_wait(&ready);
  execl(executable,executable,"after_exec",expected_pid,NULL);_exit(127);
}
int main(int argc,char**argv) {
  assert(argc>=2);setbuf(stdout,NULL);executable=argv[0];
  if(!strcmp(argv[1],"after_exec")) {
    assert(argc==3&&getpid()==atoi(argv[2]));observation();
    printf("exec_survivor %d\n",getpid());return 0;
  }
  if(!strcmp(argv[1],"nonleader")||!strcmp(argv[1],"exec_race")) {
    snprintf(expected_pid,sizeof expected_pid,"%d",getpid());
    unsigned count=!strcmp(argv[1],"exec_race")?2:1;
    assert(!pthread_barrier_init(&ready,NULL,count+1));pthread_t threads[2];
    for(unsigned i=0;i<count;i++)assert(!pthread_create(threads+i,NULL,exec_thread,NULL));
    pthread_barrier_wait(&ready);for(;;)pause();
  }
  if(!strcmp(argv[1],"job")) {
    printf("ready %d\n",getpid());char go;assert(read(0,&go,1)==1);
    observation();printf("resumed %d\n",getpid());return 0;
  }
  if(!strcmp(argv[1],"victim")) {
    pid_t child=fork();assert(child>=0);
    if(!child) {
      void*p=mmap(NULL,64*1024*1024,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
      assert(p!=MAP_FAILED);printf("victim %d\n",getpid());
      for(;;)observation();
    }
    int status;assert(waitpid(child,&status,0)==child);
    assert(WIFSIGNALED(status)&&WTERMSIG(status)==SIGKILL);
    observation();puts("victim_retired");return 0;
  }
  return 2;
}
