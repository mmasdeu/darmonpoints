#########################################################################
#       Copyright (C) 2024 Marc Masdeu
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#                  http://www.gnu.org/licenses/
#########################################################################
from copy import deepcopy

from sage.categories.pushout import pushout
from sage.matrix.constructor import Matrix
from sage.matrix.matrix_space import MatrixSpace
from sage.misc.all import cputime
from sage.misc.cachefunc import cached_function, cached_method
from sage.misc.misc_c import prod
from sage.misc.verbose import get_verbose, set_verbose, verbose
from sage.modules.free_module_element import FreeModuleElement_generic_dense
from sage.modules.free_module_element import free_module_element as vector
from sage.modules.module import Module
from sage.modules.vector_integer_dense import Vector_integer_dense
from sage.rings.all import Integer, Zp
from sage.rings.finite_rings.integer_mod_ring import Zmod
from sage.rings.infinity import Infinity
from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import ZpCA
from sage.rings.padics.padic_generic import pAdicGeneric
from sage.rings.padics.precision_error import PrecisionError
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.rational_field import QQ
from sage.structure.element import ModuleElement
from sage.structure.parent import Parent
from sage.structure.richcmp import richcmp
from sage.structure.sage_object import load, save
from sage.structure.unique_representation import (
    CachedRepresentation,
    UniqueRepresentation,
)

from .divisors import Divisors


class RationalFunctionsElement(ModuleElement):
    def __init__(self, parent, data, check=True):
        if check:
            K = parent.base_ring()
            FF = parent._V
            z = FF.gen()
            if data == 0:
                self._value = FF(1)
            elif isinstance(data.parent(), Divisors):
                self._value = FF(1)
                for Q, n in data:
                    self._value *= (1 - z / K(Q)) ** n
            elif data.parent() == FF:
                self._value = FF(data)
        else:
            self._value = data
        ModuleElement.__init__(self, parent)

    def numerator(self):
        return self._value.numerator()

    def denominator(self):
        return self._value.denominator()

    def power_series(self, names=None):
        if names is None:
            names = "t"
        K = self.parent().base_ring()
        try:
            prec = K.precision_cap()
        except AttributeError:
            prec = 20  # DEBUG
        Ps = PowerSeriesRing(K, names, default_prec=prec)
        ans = Ps(self._value)
        return ans

    def rational_function(self):
        return self._value

    def __call__(self, D):
        return self.evaluate(D)

    def evaluate(self, D):
        if isinstance(D.parent(), Divisors):
            return prod(self._value(P) ** ZZ(n) for P, n in D)
        else:
            return self._value(D)

    def pair_with(self, D):
        return self(D).log(0)

    def _cmp_(self, right):
        return (self._value > right._value) - (self._value < right._value)

    def __nonzero__(self):
        return self._value != 1

    def _add_(self, right):
        ans = self._value * right._value
        return self.__class__(self.parent(), ans, check=False)

    def _sub_(self, right):
        ans = self._value / right._value
        return self.__class__(self.parent(), ans, check=False)

    def _neg_(self):
        ans = self._value**-1
        return self.__class__(self.parent(), ans, check=False)

    def _repr_(self):
        return repr(self._value)

    def scale_by(self, k):
        ans = self._value**k
        return self.__class__(self.parent(), ans, check=False)

    def _acted_upon_(self, g, on_left):
        assert not on_left
        if isinstance(g, Integer):
            return self.scale_by(g)
        else:
            return self.left_act_by_matrix(g)

    def left_act_by_matrix(self, g):  # rational functions
        Ps = self._value.parent()
        K = Ps.base_ring()
        # Below we code the action which is compatible with the usual action
        # P |-> (aP+b)/(cP+D)
        z = self._value.parent().gen()
        a, b, c, d = g.list()
        num, den = self._value.numerator(), self._value.denominator()
        assert num.degree() == den.degree()
        deg = num.degree()
        new_num = sum(
            ai * (d * z - b) ** i * (-c * z + a) ** (deg - i)
            for ai, i in zip(num.coefficients(), num.exponents())
        )
        new_num /= new_num(0)
        new_den = sum(
            ai * (d * z - b) ** i * (-c * z + a) ** (deg - i)
            for ai, i in zip(den.coefficients(), den.exponents())
        )
        new_den /= new_den(0)
        try:
            ans = new_num / new_den
        except ZeroDivisionError:
            print(f"{den = }")
            print(f"{a = }, {b = }, {c = }, {d = }")
            print(new_den)
            assert 0
        return self.__class__(self.parent(), ans, check=False)


class RationalFunctions(Parent, CachedRepresentation):
    r""" """
    Element = RationalFunctionsElement

    def __init__(self, K):
        Parent.__init__(self)
        self._base_ring = K
        self._V = PolynomialRing(K, names="z")

    def base_ring(self):
        return self._base_ring

    def _element_constructor_(self, data):
        return self.element_class(self, data)

    def _repr_(self):
        return "Field of Rational Functions over %s" % (self._base_ring)
