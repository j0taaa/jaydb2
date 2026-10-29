#define _GNU_SOURCE
#include "stage_control.h"
#include "window.h"
#include <assert.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <time.h>
#include <unistd.h>
static struct jayacct_u128 words(__uint128_t n){return(struct jayacct_u128){n,n>>64};}
static __uint128_t wide(struct jayacct_u128 n){return ((__uint128_t)n.hi<<64)|n.lo;}
int main(int argc,char**argv){
 assert(argc==2);int socket_fd=socket(AF_UNIX,SOCK_SEQPACKET,0);assert(socket_fd>=0);
 struct sockaddr_un address={.sun_family=AF_UNIX};assert(strlen(argv[1])<sizeof address.sun_path);strcpy(address.sun_path,argv[1]);
 assert(!connect(socket_fd,(struct sockaddr*)&address,sizeof address));
 int writable=memfd_create("stage-inflight",0);assert(writable>=0);char data[4096]={42};assert(write(writable,data,sizeof data)==sizeof data);
 char path[80];snprintf(path,sizeof path,"/proc/self/fd/%d",writable);int readonly=open(path,O_RDONLY);assert(readonly>=0);assert(!close(writable));
 struct iovec iov={.iov_base=(void*)"F",.iov_len=1};char ancillary[CMSG_SPACE(sizeof(int))]={0};
 struct msghdr msg={.msg_iov=&iov,.msg_iovlen=1,.msg_control=ancillary,.msg_controllen=sizeof ancillary};
 struct cmsghdr*c=CMSG_FIRSTHDR(&msg);c->cmsg_level=SOL_SOCKET;c->cmsg_type=SCM_RIGHTS;c->cmsg_len=CMSG_LEN(sizeof(int));memcpy(CMSG_DATA(c),&readonly,sizeof readonly);
 assert(sendmsg(socket_fd,&msg,0)==1);char ack;assert(read(socket_fd,&ack,1)==1&&ack=='A');
 const void*page;assert(!jaystage_map(atoi(getenv("JAYDB_ACCOUNTING_STAGE_FD")),&page));
 struct jayacct_window_snapshot window;assert(!jayacct_window_barrier(&window));
 struct timespec t;assert(!clock_gettime(CLOCK_MONOTONIC,&t));__uint128_t start=(__uint128_t)t.tv_sec*1000000000u+t.tv_nsec;
 struct jaystage_request request={.abi=1,.stage=3,.scope_id=window.scope_id,.generation={1,0},.start_ns=words(start),.deadline_ns=words(start+100000000u)};
 struct jaystage_receipt receipt;assert(!jaystage_arm(&request,&receipt));assert(write(socket_fd,"T",1)==1);
 snprintf(path,sizeof path,"/proc/self/fd/%d",readonly);assert(!truncate(path,0));
 assert(!jayacct_window_barrier(&window));assert(!jaystage_read(page,&receipt));
 assert(receipt.state==JAYSTAGE_EXPIRED_RECOVERED&&wide(receipt.observed_ns)>=wide(request.deadline_ns));
 assert(receipt.recovery_sequence.lo>receipt.arm_sequence.lo);assert(!jaystage_retire(&request,&receipt));
 assert(!close(readonly));assert(!close(socket_fd));assert(!jayacct_window_end(&window));assert(!jaystage_unmap(page));
 puts("inflight_real_return_cleanup");return 0;
}
