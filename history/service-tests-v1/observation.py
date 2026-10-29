"""Observe actual root assignments without changing the controller's decisions."""
from tools.service.controller import Database
from pathlib import Path
import tempfile


def fixture_loading():
    """Explicit test installation, before constructing any Database.

    The NODELETE shim remains a process baseline after its temporary file is
    removed. Production callers install their pinned artifact separately.
    """
    from tools.service.build_loading import build
    from tools.service.loading import Runtime
    with tempfile.TemporaryDirectory(prefix='jaydb-test-loader-install-') as directory:
        artifact=Path(directory)/'loading.so'
        runtime=Runtime.load(artifact,manifest=build(artifact))
        from tests.service.runtime_profile import fixture_lifecycle
        fixture_lifecycle(runtime)
        return runtime


class PublicationObservedDatabase(Database):
    def __init__(self, *args, **kwargs):
        self.root_assignments = 0
        super().__init__(*args, **kwargs)

    @property
    def state(self):
        return self._observed_state

    @state.setter
    def state(self, value):
        self.root_assignments += 1
        self._observed_state = value
