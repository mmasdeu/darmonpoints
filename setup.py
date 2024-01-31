from setuptools import setup
from Cython.Build import cythonize
import os.path

setup(
    ext_modules = cythonize(os.path.join("darmonpoints", "*.pyx"))
)
