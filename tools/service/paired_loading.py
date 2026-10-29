"""Load a builder-paired receipt shim without compiling at runtime."""
from pathlib import Path

from .loading import IdentityMismatch,Runtime


def runtime_for(artifact,report):
    dependency=report.get('loading')
    if not isinstance(dependency,dict):
        raise IdentityMismatch('Artifact lacks its pinned loading runtime')
    name=dependency.get('file')
    if not isinstance(name,str) or not name or Path(name).name!=name:
        raise IdentityMismatch('Loading runtime must be paired beside its artifact')
    return Runtime.load(Path(artifact).parent/name,manifest=dependency.get('manifest'))
