#include "stage_control.h"
#include <string.h>
int jaystage_arm(const struct jaystage_request*r,struct jaystage_receipt*out) {
  return jaystage_raw_call(r,out,JAYSTAGE_ARM);
}
int jaystage_retire(const struct jaystage_request*r,struct jaystage_receipt*out) {
  return jaystage_raw_call(r,out,JAYSTAGE_RETIRE);
}
int jaystage_read(const void*page,struct jaystage_receipt*out) {
  if(!page||!out)return EINVAL;
  const struct jaystage_shared*s=page;
  for(;;) {
    uint64_t before=atomic_load_explicit(&s->sequence,memory_order_acquire);
    if(before&1)continue;
    for(unsigned i=0;i<JAYSTAGE_RECEIPT_WORDS;i++) {
      uint64_t value=atomic_load_explicit(&s->receipt[i],memory_order_relaxed);
      memcpy((char*)out+i*sizeof value,&value,sizeof value);
    }
    atomic_thread_fence(memory_order_acquire);
    if(before==atomic_load_explicit(&s->sequence,memory_order_acquire))break;
  }
  return out->abi==JAYSTAGE_ABI?0:ENOTSUP;
}
#include <sys/mman.h>
int jaystage_map(int fd,const void **out) {
  if(!out)return EINVAL;
  void*p=mmap(NULL,JAYSTAGE_SHARED_BYTES,PROT_READ,MAP_SHARED,fd,0);
  if(p==MAP_FAILED)return errno;
  *out=p;return 0;
}
int jaystage_unmap(const void*page) {
  if(!page)return EINVAL;
  return munmap((void*)page,JAYSTAGE_SHARED_BYTES)?errno:0;
}
