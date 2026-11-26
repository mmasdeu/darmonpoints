import os
import os.path
import sys

from Cython.Build import cythonize
from setuptools import Extension, setup
from setuptools.command.build_ext import build_ext

# Directories where GMP (gmp.h, libgmp) is looked for, besides the compiler's
# default ones: the prefix of the python environment (conda, Sage venv) and
# $GMP_PREFIX or $SAGE_LOCAL when they are set.
_prefixes = [os.environ.get("GMP_PREFIX"), os.environ.get("SAGE_LOCAL"), sys.prefix, sys.base_prefix]
_prefixes = [p for i, p in enumerate(_prefixes) if p and p not in _prefixes[:i]]
GMP_INCLUDE_DIRS = [d for d in (os.path.join(p, "include") for p in _prefixes) if os.path.isdir(d)]
GMP_LIBRARY_DIRS = [d for d in (os.path.join(p, "lib") for p in _prefixes) if os.path.isdir(d)]

# Extensions whose failure to build does not stop the installation: the
# package then uses its pure python fallback (with the same results).
OPTIONAL_EXTENSIONS = {"darmonpoints.sparse_padic"}


class build_ext_optional(build_ext):
    def build_extension(self, ext):
        try:
            super().build_extension(ext)
        except Exception as e:
            if ext.name not in OPTIONAL_EXTENSIONS:
                raise
            print(
                f"WARNING: the optional extension {ext.name} was not built ({type(e).__name__}: {e}).\n"
                "darmonpoints will use the (slower) pure python code instead, with the same results.\n"
                "To build it, install GMP (gmp.h and libgmp) and set GMP_PREFIX to its prefix if needed.",
                file=sys.stderr,
            )


extensions = [
    Extension("darmonpoints.mixed_extension", [os.path.join("darmonpoints", "mixed_extension.pyx")]),
    Extension("darmonpoints.sparse", [os.path.join("darmonpoints", "sparse.pyx")]),
    Extension(
        "darmonpoints.sparse_padic",
        [os.path.join("darmonpoints", "sparse_padic.pyx")],
        libraries=["gmp"],
        include_dirs=GMP_INCLUDE_DIRS,
        library_dirs=GMP_LIBRARY_DIRS,
    ),
]

setup(
    ext_modules=cythonize(extensions),
    cmdclass={"build_ext": build_ext_optional},
)
