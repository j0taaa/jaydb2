/* Cooperative cancellation: the signal only sets a flag. No asynchronous
 * longjmp is permitted through acquisition -> owner publication or counter
 * publication. Explicit safepoints run outside those critical sections. */
static void deadline_signal(int signal) {(void)signal;deadline_signalled=1;}
static void stage_child_signal(int signal) {(void)signal;}
/* This observer-only wake must not change what exec-root inherits. Capture
 * the complete prior action while installing it; restore only before exec in
 * the fork child. Linux exec, not a post-exec pointer restore, resets caught
 * handlers and preserves SIG_IGN. The inherited process mask is untouched. */
static struct sigaction stage_root_sigchld;
static void deadline_initialize(void) {
  struct sigaction action={0};action.sa_handler=deadline_signal;
  if(sigemptyset(&action.sa_mask)||sigaction(SIGALRM,&action,NULL))fail("deadline signal setup");
  sigset_t set;if(sigemptyset(&set)||sigaddset(&set,SIGALRM)||sigprocmask(SIG_UNBLOCK,&set,NULL))
    fail("deadline signal mask");
  if(stage_control) {
    struct sigaction child={0};child.sa_handler=stage_child_signal;
    if(sigemptyset(&child.sa_mask)||sigaction(SIGCHLD,&child,&stage_root_sigchld))fail("stage child wake setup");
  }
  struct sigevent event={0};event.sigev_notify=SIGEV_SIGNAL;event.sigev_signo=SIGALRM;
  if(syscall(SYS_timer_create,CLOCK_MONOTONIC,&event,&deadline_timer))fail("deadline timer creation");
}
static void deadline_tick(void) {
  if(lifecycle_depth||(!deadline_task&&stage_receipt.state!=JAYSTAGE_ARMED))return;
  if(!deadline_signalled&&(++deadline_steps&63))return;
  struct timespec now;
  if(clock_gettime(CLOCK_MONOTONIC,&now)||now.tv_sec<0)fail("deadline observation clock");
  __uint128_t observed=(__uint128_t)now.tv_sec*1000000000u+now.tv_nsec;
  deadline_signalled=0;
  if(observed>=deadline_ns){cancellation_ns=observed;siglongjmp(deadline_escape,1);}
}
static void deadline_maybe_arm(void) {
  struct task*t=last_stopped;
  if(!t||t->dead||!t->stopped||!t->entry||!t->marker||!t->deadline_marker)return;
  if(deadline_task){if(deadline_task!=t)fail("concurrent deadline markers require caller serialization");return;}
  deadline_task=t;deadline_prior_active=active;
  deadline_begin_publications=snapshots;
  deadline_rearm();
}
static void deadline_rearm(void) {
  bool armed=deadline_task||stage_receipt.state==JAYSTAGE_ARMED;
  __uint128_t until=deadline_task?((__uint128_t)deadline_task->args[4]<<64)|deadline_task->args[3]:~(__uint128_t)0;
  if(stage_receipt.state==JAYSTAGE_ARMED&&wide(stage_receipt.deadline_ns)<until)
    until=wide(stage_receipt.deadline_ns);
  deadline_ns=until;deadline_steps=0;deadline_signalled=1;
  struct itimerspec timer={0};
  __uint128_t end=((__uint128_t)1<<63)*1000000000u;
  if(armed&&until<end) {
    /* An all-zero it_value disarms POSIX timers. deadline_tick observes the
     * original zero/past deadline; 1ns only wakes a blocking wait. */
    __uint128_t wake=until?until:1;
    timer.it_value.tv_sec=(time_t)(wake/1000000000u);
    timer.it_value.tv_nsec=(long)(wake%1000000000u);
  }
  if(syscall(SYS_timer_settime,deadline_timer,TIMER_ABSTIME,&timer,NULL))fail("deadline timer arm");
}
static void deadline_disarm(void) {
  if(deadline_task)deadline_task->deadline_marker=false;
  deadline_task=NULL;deadline_prior_active=NULL;deadline_signalled=0;
  deadline_rearm();
}
static bool marker_exit(struct task*t) {
  while(!t->dead&&t->entry&&!t->exiting) {
    if(t->stopped)resume(t);
    wait_one();
  }
  return !t->dead&&!t->exiting&&t->stopped;
}
static bool marker_error(struct task*t,int error) {
  if(!marker_exit(t))return false;
  struct user_regs_struct regs;
  if(ptrace(PTRACE_GETREGS,t->pid,0,&regs)<0) {
    if(errno==ESRCH){unstable(t);return false;}fail("cancelled marker registers");
  }
  regs.rax=(uint64_t)-(int64_t)error;
  if(ptrace(PTRACE_SETREGS,t->pid,0,&regs)<0) {
    if(errno==ESRCH){unstable(t);return false;}fail("cancelled marker result");
  }
  /* Invalidate stale caller output; no snapshot or peak was manufactured. */
  if(ptrace(PTRACE_POKEDATA,t->pid,(void*)(uintptr_t)t->args[1],0)<0) {
    if(errno==ESRCH){unstable(t);return false;}fail("cancelled marker output");
  }
  t->marker=false;t->memory=false;t->deadline_marker=false;t->marker_hold_started=false;
  return true;
}
static void deadline_cancel(void) {
  struct task*t=deadline_task,*prior=deadline_prior_active;
  __uint128_t observed=cancellation_ns, expired_deadline=deadline_ns;
  bool discarded=snapshot_in_progress;
  bool stage_due=stage_receipt.state==JAYSTAGE_ARMED&&observed>=wide(stage_receipt.deadline_ns);
  bool marker_due=t&&observed>=(((__uint128_t)t->args[4]<<64)|t->args[3]);
  uint64_t pending_flags=stage_due?stage_pending_flags():0;
  if(stage_due) {
    stage_receipt.state=JAYSTAGE_EXPIRED_PENDING_RECOVERY;
    stage_receipt.observed_ns=words(observed);
    stage_receipt.pending_flags=pending_flags;
    ++stage_receipt.cancellations;stage_recovery=true;stage_publish();
  }
  deadline_disarm();
  if(t&&!marker_due) {
    deadline_task=t;deadline_prior_active=prior;t->deadline_marker=true;deadline_rearm();
  }
  if(snapshot_in_progress) {
    regions=previous;retained=previous_retained;bank_index^=1;snapshot_in_progress=false;
    /* O(1) rollback. A partial scan may have changed cached live flags. Until
     * a complete scan rebuilds them, metadata factories acquire fresh records
     * instead of reusing an identity that might still have a real owner. */
    caches_dirty=true;
  }
  if(scan_fd>=0){close(scan_fd);scan_fd=-1;}
  ++deadline_cancellations;
  if(report_fd>=0) {
    char*p=output_buffer;p=literal(p,"{\"type\":\"cancellation\",\"pid\":");p=decimal(p,(unsigned)(t?t->pid:stage_receipt.owner_pid));
    p=literal(p,",\"error\":110,\"observed_ns\":\"");p=decimal(p,observed);
    p=literal(p,"\",\"deadline_ns\":\"");p=decimal(p,expired_deadline);
    p=literal(p,"\",\"output_valid\":false,\"discarded_partial_scan\":");p=literal(p,discarded?"true":"false");
    p=literal(p,",\"valid_publications_since_arm\":");p=decimal(p,snapshots-deadline_begin_publications);
    p=literal(p,"}\n");write_all(report_fd,output_buffer,(size_t)(p-output_buffer));
  }
  if(stage_due)stage_log("expired_pending_recovery");
  if(marker_due&&!stage_terminal) {
    active=prior!=t&&prior&&!prior->dead?prior:NULL;
    if(marker_error(t,ETIMEDOUT))resume(t);
  }
}
static void release_hold(struct task*t) {
  if(deadline_task)fail("release overlaps a deadline marker");
  bool owned=hold_owner==t->pid;
  if(!marker_exit(t))return;
  if(!owned){if(marker_error(t,EPERM))resume(t);return;}
  if(ptrace(PTRACE_POKEDATA,t->pid,(void*)(uintptr_t)t->args[1],(void*)(uintptr_t)JAYACCT_MARKER)<0) {
    if(errno==ESRCH){unstable(t);return;}fail("hold release receipt");
  }
  t->marker=false;t->memory=false;t->deadline_marker=false;t->marker_hold_started=false;
  hold_owner=0;active=NULL;
  log_lifecycle("hold_released",t->pid,0,t->space->uid);
  /* A stopped memory-syscall ENTRY must still go through the global scheduler.
   * Releasing a hold is not permission to run several mutations concurrently. */
  for(struct task*other=tasks;other;other=other->next)
    if(!(other->entry&&other->memory)&&!other->exiting)resume(other);
}
