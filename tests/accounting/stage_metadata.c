#define _GNU_SOURCE
#include "stage_control.h"
#include "window.h"
#include <assert.h>
#include <linux/io_uring.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
int main(void){
 struct jayacct_window_snapshot window;assert(!jayacct_window_barrier(&window));
 struct timespec t;assert(!clock_gettime(CLOCK_MONOTONIC,&t));__uint128_t now=(__uint128_t)t.tv_sec*1000000000u+t.tv_nsec;
 struct jaystage_request req={.abi=1,.stage=3,.scope_id=window.scope_id,.generation={1,0},.start_ns={now,now>>64},.deadline_ns={now+100000000u,(now+100000000u)>>64}};
 struct jaystage_receipt receipt;assert(!jaystage_arm(&req,&receipt));
 pid_t p=fork();assert(p>=0);
 if(!p){struct io_uring_params params={0};long fd=syscall(SYS_io_uring_setup,4,&params);assert(fd>=0);close((int)fd);_exit(0);}
 int s;assert(waitpid(p,&s,0)==p);puts("parent_returned");return 0;
}
