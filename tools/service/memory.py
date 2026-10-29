"""Historical peaks for one real allocation window, never RSS estimates.

The reader observes the counter's last published instant. This can justify
interrupting a helper after a transient excess; it is not a pre-construction
barrier and must not be used to authorize a Campo store. INCOMPLETE remains an
error, including when the numeric amount would be above the public ceiling.
"""
from tools.accounting.client import FROZEN


class InvalidMemoryObservation(RuntimeError):
    pass


def validate(window, scope):
    window.require_scope(scope).require_complete()
    current=window.snapshot
    upper_sequence=window.end_sequence if window.state==2 else current.sequence
    upper_time=window.end_monotonic_ns if window.state==2 else current.monotonic_ns
    if (window.state not in (1,2) or not window.begin_sequence
            or not window.begin_sequence<=window.peak_sequence<=upper_sequence
            or not window.begin_monotonic_ns<=window.peak_monotonic_ns<=upper_time
            or upper_sequence>current.sequence or upper_time>current.monotonic_ns
            or (window.active and current.current>window.peak)
            or not current.flags&FROZEN or not window.peak_flags&FROZEN):
        raise InvalidMemoryObservation('Allocation window has inconsistent provenance')
    return window


class MemoryExcess(RuntimeError):
    def __init__(self,window,ceiling,scope):
        window=validate(window,scope)
        witness=window.excess_witness(ceiling)
        if witness is None:
            raise ValueError('A memory limit requires a real strict excess in this scope')
        self.window,self.witness,self.ceiling=window,witness,ceiling
        self.measured=witness.amount
        super().__init__('Observed allocation-window peak exceeds its public ceiling')


class MemoryWindow:
    """The trusted host supplies the inherited counter and exact active scope.

    No scope is silently opened/replaced, no global peak is substituted, and
    no coverage flag is cleared. The owner closes its scope through the final
    native completion boundary. Construct this only for the selected counter;
    accepting arbitrary client-provided observations is not an admission API.
    """
    def __init__(self,counter,scope,ceiling):
        if type(scope) is not int or not 0<scope<2**128:
            raise ValueError('An exact allocation scope is required')
        if type(ceiling) is not int or ceiling<0:
            raise ValueError('Memory ceiling must be a Nat')
        self.counter,self.scope,self.ceiling=counter,scope,ceiling

    def poll(self):
        window=validate(self.counter.window_read(),self.scope)
        if not window.active:
            raise InvalidMemoryObservation('Helper monitoring requires its active allocation scope')
        if window.excess_witness(self.ceiling) is not None:
            raise MemoryExcess(window,self.ceiling,self.scope)
        return window
