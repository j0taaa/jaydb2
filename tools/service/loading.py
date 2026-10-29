"""One synchronous owner for one Linux dlopen reference."""
from contextlib import contextmanager
import ctypes
from _ctypes import dlclose
import os
from pathlib import Path


class OwnershipError(RuntimeError):
    """Ownership is unresolved. Stop the instance; never retry consumption."""


class LibraryOwner:
    def __init__(self, path):
        self._busy = self._uncertain = False
        self._library = ctypes.CDLL(str(Path(path).resolve()),
                                    mode=os.RTLD_NOW | os.RTLD_LOCAL)

    @contextmanager
    def using(self):
        if self._busy or self._uncertain or self._library is None:
            raise OwnershipError('Native library is closed, uncertain or already in use')
        self._busy = True
        try:
            yield self._library
        finally:
            self._busy = False

    def poison(self):
        self._uncertain = True

    def close(self):
        if self._busy or self._uncertain:
            raise OwnershipError('Cannot unload a native library still in use or uncertain')
        if self._library is None:
            return
        # Mark before consumption. An exceptional return cannot authorize a
        # second dlclose against a handle the first attempt may have consumed.
        self._uncertain = True
        try:
            dlclose(self._library._handle)
        except BaseException as error:
            raise OwnershipError('Native unload is uncertain; never retry') from error
        self._library = None
        self._uncertain = False

    def __enter__(self):
        return self

    def __exit__(self, *exception):
        self.close()
