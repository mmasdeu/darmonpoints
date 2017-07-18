## -*- encoding: utf-8 -*-
import os
import sys
from setuptools import setup
from codecs import open # To open the README file with proper encoding
from setuptools.command.test import test as TestCommand # for tests

# The next block is if there are some cython files

from setuptools import Extension
from Cython.Build import cythonize
import Cython.Compiler.Options
from sage.env import sage_include_directories

# Get information from separate files (README, VERSION)
def readfile(filename):
    with open(filename,  encoding='utf-8') as f:
        return f.read()

# For the tests
class SageTest(TestCommand):
    def run_tests(self):
        errno = os.system("sage -t --force-lib darmonpoints darmonpoints/*.pyx")
        if errno != 0:
            sys.exit(1)

 # Cython modules
ext_modules = [
         Extension('darmonpoints.mixed_extension',
         sources = [os.path.join('darmonpoints','mixed_extension.pyx')],
         include_dirs=sage_include_directories())
]

setup(
    name = "darmonpoints",
    version = readfile("VERSION"), # the VERSION file is shared with the documentation
    description='Compute non-archimedean Darmon points',
    long_description = readfile("README.rst"), # get the long description from the README
    url='https://github.com/mmasdeu/darmonpoints',
    author='Marc Masdeu',
    author_email='marc.masdeu@gmail.com', # choose a main contact email
    license='GPLv2+', # This should be consistent with the LICENCE file
    classifiers=[
      # How mature is this project? Common values are
      #   3 - Alpha
      #   4 - Beta
      #   5 - Production/Stable
      'Development Status :: 4 - Beta',
      'Intended Audience :: Science/Research',
      'Topic :: Scientific/Engineering :: Mathematics',
      'License :: OSI Approved :: GNU General Public License v2 or later (GPLv2+)',
      'Programming Language :: Python :: 2.7',
    ], # classifiers list: https://pypi.python.org/pypi?%3Aaction=list_classifiers
    keywords = "SageMath, Darmon points, elliptic curves, p-adic periods",
    requires = ['sagemath (>=7.6)'],
    packages = ['darmonpoints'],
    ext_modules = cythonize(ext_modules),
    include_package_data = True,
    cmdclass = {'test': SageTest} # adding a special setup command for tests
)
