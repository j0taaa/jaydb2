"""Explicit offline installation for host-consumer tests, never production."""
from pathlib import Path
import resource
import tempfile


def fixture_lifecycle(loading_runtime=None):
    from tools.service.build_lifecycle import build
    from tools.service.lifecycle import LifecycleRuntime
    from tools.service.loading import Runtime
    from tools.service.build_loading import build as build_loading
    # The tests exercise the same selected core profile, without reducing hard.
    _, hard = resource.getrlimit(resource.RLIMIT_CORE)
    resource.setrlimit(resource.RLIMIT_CORE, (0, hard))
    with tempfile.TemporaryDirectory(prefix='jaydb-test-lifecycle-install-') as directory:
        root = Path(directory)
        if loading_runtime is None:
            loader = root/'loading.so'
            loading_runtime = Runtime.load(loader, manifest=build_loading(loader))
        path = root/'lifecycle.so'
        return LifecycleRuntime.load(path, manifest=build(path), loading_runtime=loading_runtime)
