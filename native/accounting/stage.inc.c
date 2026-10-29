/* Opt-in stage control. Included after the ordinary deadline implementation.
 * Control receipts never close a window or stand in for a memory snapshot. */
static void stage_publish(void) {
  if(!stage_page)return;
  atomic_fetch_add_explicit(&stage_page->sequence,1,memory_order_acq_rel);
  for(unsigned i=0;i<JAYSTAGE_RECEIPT_WORDS;i++) {
    uint64_t value;memcpy(&value,(char*)&stage_receipt+i*sizeof value,sizeof value);
    atomic_store_explicit(&stage_page->receipt[i],value,memory_order_relaxed);
  }
  atomic_fetch_add_explicit(&stage_page->sequence,1,memory_order_release);
}
static uint64_t stage_pending_flags(void) {
  uint64_t flags=0;
  if(snapshot_in_progress)flags|=JAYSTAGE_PENDING_SCAN;
  if(hold_owner)flags|=JAYSTAGE_PENDING_HOLD;
  if(pending||stage_terminal)flags|=JAYSTAGE_PENDING_METADATA;
  if(active&&!active->dead&&!active->stopped&&active->memory)
    flags|=JAYSTAGE_PENDING_INFLIGHT;
  for(struct task*t=tasks;t;t=t->next)if(!t->dead) {
    if(t!=stage_owner&&t->entry&&t->memory&&!t->marker)flags|=JAYSTAGE_PENDING_INFLIGHT;
    if(t->vfork_wait)flags|=JAYSTAGE_PENDING_VFORK;
    if(t->creation_pending||t->exit_result_missing)flags|=JAYSTAGE_PENDING_METADATA;
    if(!t->stopped)flags|=JAYSTAGE_PENDING_STOP;
  }
  return flags;
}
static void stage_log(const char*event) {
  if(report_fd<0)return;
  char*p=output_buffer;p=literal(p,"{\"type\":\"stage\",\"event\":\"");p=literal(p,event);
  p=literal(p,"\",\"generation\":\"");p=decimal(p,wide(stage_receipt.generation));
  p=literal(p,"\",\"scope_id\":\"");p=decimal(p,wide(stage_receipt.scope_id));
  p=literal(p,"\",\"state\":");p=decimal(p,stage_receipt.state);
  p=literal(p,",\"observed_ns\":\"");p=decimal(p,wide(stage_receipt.observed_ns));
  p=literal(p,"\",\"deadline_ns\":\"");p=decimal(p,wide(stage_receipt.deadline_ns));
  p=literal(p,"\",\"pending_flags\":");p=decimal(p,stage_receipt.pending_flags);
  p=literal(p,",\"recovery_sequence\":\"");p=decimal(p,wide(stage_receipt.recovery_sequence));
  p=literal(p,"\",\"memory_observation\":false}\n");
  write_all(report_fd,output_buffer,(size_t)(p-output_buffer));
}
static void stage_prepare(struct task*t) {
  t->stage_prepared=true;
  if(t->pid!=root_pid||t->tgid!=root_pid) {t->stage_error=EPERM;return;}
  if(!remote_copy(t,t->args[3],&stage_request,sizeof stage_request)) {t->stage_error=EFAULT;return;}
  if(stage_request.abi!=JAYSTAGE_ABI||!stage_request.stage||
      !wide(stage_request.generation)) {t->stage_error=EINVAL;return;}
  if(jayacct_window_read(counter,&latest_window))fail("stage window read");
  if(latest_window.state!=JAYACCT_WINDOW_ACTIVE||
      wide(latest_window.scope_id)!=wide(stage_request.scope_id)) {t->stage_error=ESTALE;return;}
  if(t->args[2]==JAYSTAGE_RETIRE) {
    if(stage_owner!=t||stage_receipt.owner_mm!=t->space->uid||
        wide(stage_receipt.generation)!=wide(stage_request.generation)||
        memcmp(&stage_request.scope_id,&stage_receipt.scope_id,sizeof(struct jayacct_u128))||
        stage_receipt.stage!=stage_request.stage||
        wide(stage_receipt.start_ns)!=wide(stage_request.start_ns)||
        wide(stage_receipt.deadline_ns)!=wide(stage_request.deadline_ns))t->stage_error=ESTALE;
    return;
  }
  if(t->args[2]!=JAYSTAGE_ARM) {t->stage_error=EINVAL;return;}
  if(wide(stage_request.generation)<=wide(stage_receipt.generation)) {t->stage_error=ESTALE;return;}
  if(stage_receipt.state!=JAYSTAGE_IDLE&&stage_receipt.state!=JAYSTAGE_RETIRED) {
    t->stage_error=EBUSY;return;
  }
  struct timespec now;
  if(clock_gettime(CLOCK_MONOTONIC,&now)||now.tv_sec<0)fail("stage arm clock");
  __uint128_t observed=(__uint128_t)now.tv_sec*1000000000u+now.tv_nsec;
  if(wide(stage_request.start_ns)>observed||wide(stage_request.deadline_ns)<wide(stage_request.start_ns)) {
    t->stage_error=EINVAL;return;
  }
  struct stage_origin*origin=stage_origins;
  for(;origin;origin=origin->next) {
    if(origin->request.stage==stage_request.stage&&
        wide(origin->request.scope_id)==wide(stage_request.scope_id))break;
  }
  if(origin) {
    if(wide(origin->request.start_ns)!=wide(stage_request.start_ns)||
        wide(origin->request.deadline_ns)!=wide(stage_request.deadline_ns)) {t->stage_error=EPERM;return;}
  } else {
    origin=allocate(&persistent,sizeof *origin);origin->request=stage_request;
    origin->next=stage_origins;stage_origins=origin;
  }
  deadline_begin_publications=snapshots;
  stage_owner=t;
  stage_receipt=(struct jaystage_receipt){.abi=JAYSTAGE_ABI,.state=JAYSTAGE_ARMED,
    .stage=stage_request.stage,.scope_id=stage_request.scope_id,.generation=stage_request.generation,
    .start_ns=stage_request.start_ns,.deadline_ns=stage_request.deadline_ns,
    .arm_sequence=latest.sequence,.owner_pid=(uint64_t)t->pid,.owner_mm=t->space->uid};
  stage_publish();deadline_rearm();stage_log("armed");
}
static void stage_recovered(void) {
  if(!stage_recovery)return;
  stage_receipt.pending_flags=stage_pending_flags();
  if(!stage_receipt.pending_flags) {
    stage_receipt.state=JAYSTAGE_EXPIRED_RECOVERED;
    stage_receipt.recovery_sequence=latest.sequence;
    stage_recovery=false;stage_publish();stage_log("recovered");
  } else stage_publish();
}
static bool stage_finish(struct task*t) {
  struct jaystage_receipt out=stage_receipt;
  if(!t->stage_error&&t->args[2]==JAYSTAGE_RETIRE) {
    /* A real validated exit scan preceded this call. Pending transactions or
     * holds cannot be hidden by retiring control state. */
    uint64_t flags=stage_pending_flags();
    if(stage_recovery||flags||stage_receipt.state==JAYSTAGE_RETIRED||
        stage_receipt.state==JAYSTAGE_IDLE)t->stage_error=EBUSY;
    else {
      stage_receipt.state=JAYSTAGE_RETIRED;stage_receipt.pending_flags=0;
      stage_publish();stage_log("retired");deadline_rearm();out=stage_receipt;
    }
  }
  out.error=(uint64_t)t->stage_error;
  return copy_snapshot(t,&out,sizeof out);
}
