import os
import sys

from Cython.Build import cythonize
from setuptools import setup


def _include_dirs():
    r"""
    Directories with the PARI headers (both ``<pari.h>`` and ``<pari/pari.h>``
    styles are used) and the cysignals headers.

    Override the PARI location with the environment variable ``PARI_PREFIX``.
    """
    prefix = os.environ.get("PARI_PREFIX", sys.prefix)
    dirs = [os.path.join(prefix, "include"), os.path.join(prefix, "include", "pari")]
    try:
        import cysignals

        dirs.extend(cysignals.__path__)
    except ImportError:
        pass
    try:
        # ``flint_wrap.h``, needed by the cimports from ``sage.libs.flint``
        import sage.libs.flint

        dirs.extend(sage.libs.flint.__path__)
    except ImportError:
        pass
    return dirs


def _library_dirs():
    prefix = os.environ.get("PARI_PREFIX", sys.prefix)
    return [os.path.join(prefix, "lib")]


def _cython_include_path():
    r"""
    The directory containing the ``sage`` package, so that Cython can resolve
    the (relative) cimports inside Sage's ``.pxd`` files.
    """
    try:
        import sage.libs.flint

        path = list(sage.libs.flint.__path__)[0]
        return [os.path.dirname(os.path.dirname(os.path.dirname(path)))]
    except ImportError:
        return []


extensions = cythonize(
    os.path.join("darmonpoints", "*.pyx"), include_path=_cython_include_path()
)
for ext in extensions:
    ext.include_dirs = list(ext.include_dirs) + _include_dirs()
    ext.library_dirs = list(ext.library_dirs) + _library_dirs()

setup(ext_modules=extensions)
