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
    return dirs


def _library_dirs():
    prefix = os.environ.get("PARI_PREFIX", sys.prefix)
    return [os.path.join(prefix, "lib")]


extensions = cythonize(os.path.join("darmonpoints", "*.pyx"))
for ext in extensions:
    ext.include_dirs = list(ext.include_dirs) + _include_dirs()
    ext.library_dirs = list(ext.library_dirs) + _library_dirs()

setup(ext_modules=extensions)
