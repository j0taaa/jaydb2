//! Host-only elapsed service accounting. No program, state, or worker effects.
use serde_json::{Value, json};
use std::collections::HashMap;
use std::time::{Duration, Instant};

pub trait Clock {
    /// Nondecreasing elapsed time from one process-local origin.
    fn now(&self) -> Duration;
}

pub struct Monotonic(Instant);
impl Monotonic {
    pub fn new() -> Self {
        Self(Instant::now())
    }
}
impl Clock for Monotonic {
    fn now(&self) -> Duration {
        self.0.elapsed()
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Quota {
    pub period: Duration,
    pub budget: Duration,
}

/// Owned, non-cloneable completion token. The coordinator selects it, attaches
/// fresh snapshot authentication, then consumes it once after all service work.
/// An active read may own a token while the coordinator services other reads.
#[derive(Debug)]
pub struct Attempt {
    started: Duration,
    principal: Option<String>,
    exhausted: bool,
}

pub struct ServicePolicy<C> {
    clock: C,
    quota: Option<Quota>,
    period: u128,
    used: HashMap<String, Duration>,
}

impl<C: Clock> ServicePolicy<C> {
    pub fn new(clock: C, quota: Option<Quota>) -> Self {
        if let Some(quota) = quota {
            assert!(!quota.period.is_zero() && !quota.budget.is_zero());
        }
        Self {
            clock,
            quota,
            period: 0,
            used: HashMap::new(),
        }
    }

    /// Call at selection, after queue waiting, before decoding/authentication.
    pub fn selected(&self) -> Attempt {
        Attempt {
            started: self.clock.now(),
            principal: None,
            exhausted: false,
        }
    }

    fn roll_period(&mut self, now: Duration) {
        if let Some(quota) = self.quota {
            let period = now.as_nanos() / quota.period.as_nanos();
            if period != self.period {
                self.used.clear();
                self.period = period;
            }
        }
    }

    /// The caller supplies ONLY the id from authentication of the selected
    /// snapshot. False forbids admission, registry changes, and program start.
    /// There is deliberately no reservation for already-running requests.
    pub fn authenticated(&mut self, attempt: &mut Attempt, principal: &str) -> bool {
        assert!(
            attempt.principal.is_none(),
            "authenticate each attempt once"
        );
        attempt.principal = Some(principal.to_owned());
        if let Some(quota) = self.quota {
            self.roll_period(self.clock.now());
            attempt.exhausted =
                self.used.get(principal).copied().unwrap_or_default() >= quota.budget;
        }
        !attempt.exhausted
    }

    /// Call once after worker cleanup and publication/durable commit, before
    /// any delivery or wait for earlier responses. Includes all earlier work
    /// even if authentication happened late, or admission/execution failed.
    pub fn completed(&mut self, attempt: Attempt) -> Value {
        let now = self.clock.now();
        let elapsed = now
            .checked_sub(attempt.started)
            .expect("monotonic service clock");
        self.roll_period(now);
        let quota = self.quota.and_then(|quota| {
            attempt.principal.as_ref().map(|principal| {
                let used = self.used.entry(principal.to_owned()).or_default();
                *used = used.saturating_add(elapsed);
                json!({
                    "period": self.period.to_string(),
                    "period_ns": quota.period.as_nanos().to_string(),
                    "budget_ns": quota.budget.as_nanos().to_string(),
                    "used_ns": used.as_nanos().to_string()
                })
            })
        });
        json!({
            "format": "jaydb-service-timing-v1",
            "outcome": if attempt.exhausted { "quota" } else { "ordinary" },
            "elapsed_ns": elapsed.as_nanos().to_string(),
            "principal": attempt.principal,
            "quota": quota
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::rc::Rc;

    #[derive(Clone)]
    struct Manual(Rc<Cell<Duration>>);
    impl Clock for Manual {
        fn now(&self) -> Duration {
            self.0.get()
        }
    }
    impl Manual {
        fn at(&self, ns: u64) {
            self.0.set(Duration::from_nanos(ns));
        }
    }
    fn policy() -> (Manual, ServicePolicy<Manual>) {
        let clock = Manual(Rc::new(Cell::new(Duration::ZERO)));
        let policy = ServicePolicy::new(
            clock.clone(),
            Some(Quota {
                period: Duration::from_nanos(100),
                budget: Duration::from_nanos(10),
            }),
        );
        (clock, policy)
    }

    #[test]
    fn measures_all_service_but_no_queue_or_delivery_time() {
        let (clock, mut policy) = policy();
        clock.at(500); // Arbitrarily long framing and queue wait.
        let mut attempt = policy.selected();
        clock.at(503); // Decode and authentication cost is charged too.
        assert!(policy.authenticated(&mut attempt, "alice"));
        clock.at(518); // Admission, compile, execution, cleanup, durability.
        let receipt = policy.completed(attempt);
        clock.at(999); // Waiting for ordered delivery and delivery add nothing.
        assert_eq!(receipt["elapsed_ns"], "18");
        assert_eq!(receipt["quota"]["used_ns"], "18");
    }

    #[test]
    fn inclusive_exhaustion_authenticated_rejections_charge_once_and_roll() {
        let (clock, mut policy) = policy();
        let mut attempt = policy.selected();
        assert!(policy.authenticated(&mut attempt, "alice"));
        clock.at(10); // Could be certificate rejection or worker failure.
        assert_eq!(policy.completed(attempt)["quota"]["used_ns"], "10");
        let mut rejected = policy.selected();
        assert!(!policy.authenticated(&mut rejected, "alice"));
        clock.at(12);
        let receipt = policy.completed(rejected);
        assert_eq!(receipt["outcome"], "quota");
        assert_eq!(receipt["quota"]["used_ns"], "12");
        clock.at(99);
        let mut before = policy.selected();
        assert!(!policy.authenticated(&mut before, "alice"));
        clock.at(100); // Exact boundary, charge only completion period.
        let receipt = policy.completed(before);
        assert_eq!(receipt["quota"]["period"], "1");
        assert_eq!(receipt["quota"]["used_ns"], "1");
        let mut after = policy.selected();
        assert!(policy.authenticated(&mut after, "alice"));
        clock.at(110);
        policy.completed(after); // New period's 1 + 10 now exceeds budget.
        clock.at(200); // A period reset must also happen at authentication.
        let mut fresh_period = policy.selected();
        assert!(policy.authenticated(&mut fresh_period, "alice"));
    }

    #[test]
    fn identity_is_fresh_but_charge_keeps_the_initial_actor() {
        let (clock, mut policy) = policy();
        let mut alice = policy.selected();
        assert!(policy.authenticated(&mut alice, "alice"));
        clock.at(11); // Program exchanges alice and bob credentials.
        policy.completed(alice);
        let mut same_credential_now_bob = policy.selected();
        assert!(policy.authenticated(&mut same_credential_now_bob, "bob"));
        clock.at(13);
        assert_eq!(
            policy.completed(same_credential_now_bob)["quota"]["used_ns"],
            "2"
        );
        let mut new_credential_now_alice = policy.selected();
        assert!(!policy.authenticated(&mut new_credential_now_alice, "alice"));
        let unauthenticated = policy.selected();
        clock.at(20);
        assert!(policy.completed(unauthenticated)["quota"].is_null());
        assert_eq!(policy.used["alice"], Duration::from_nanos(11));
    }

    #[test]
    fn active_requests_finish_with_unbounded_overshoot_and_completion_period_charge() {
        let (clock, mut policy) = policy();
        let mut first = policy.selected();
        let mut second = policy.selected();
        assert!(policy.authenticated(&mut first, "alice"));
        assert!(policy.authenticated(&mut second, "alice")); // No reservations.
        clock.at(10);
        policy.completed(second);
        clock.at(1_000_000);
        let receipt = policy.completed(first);
        assert_eq!(receipt["quota"]["used_ns"], "1000000");
        assert_eq!(receipt["quota"]["period"], "10000");
        let mut next = policy.selected();
        assert!(!policy.authenticated(&mut next, "alice"));
    }

    #[test]
    fn restart_resets_counters_and_timing_only_never_rejects_or_tracks_users() {
        let (clock, mut policy) = policy();
        let mut attempt = policy.selected();
        policy.authenticated(&mut attempt, "alice");
        clock.at(50);
        policy.completed(attempt);
        let mut restarted = ServicePolicy::new(clock.clone(), policy.quota);
        let mut attempt = restarted.selected();
        assert!(restarted.authenticated(&mut attempt, "alice"));
        let mut timing = ServicePolicy::new(clock, None);
        let mut attempt = timing.selected();
        assert!(timing.authenticated(&mut attempt, "alice"));
        assert!(timing.completed(attempt)["quota"].is_null());
        assert!(timing.used.is_empty());
    }
}
