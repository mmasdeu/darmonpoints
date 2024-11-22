#########################################################################
#       Copyright (C) 2011 Cameron Franc and Marc Masdeu
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


def evalpoly(poly, x):
    # Initialize result
    result = poly[-1]
    # Evaluate value of polynomial
    # using Horner's method
    for a in reversed(poly):
        result *= x
        result += a
    return result


class MeromorphicFunctionsElement(ModuleElement):
    def __init__(self, parent, data, parameter, check=True):
        # verbose(f'{check = }')
        ModuleElement.__init__(self, parent)
        if check:
            K = parent.base_ring()
            prec = parent._prec
            Ps = parent._Ps
            if isinstance(data.parent(), Divisors):
                phi = divisor_to_pseries(parameter, Ps.gen())
                self._value = Ps(0)
                for Q, n in data:
                    self._value += n * phi(K(Q))
                self._value = self._value.add_bigoh(prec)
                if len(data.support()) == 1:
                    self.normalize_point = Q + 1  # DEBUG
            elif data == 0:
                self._value = Ps(0)
            elif data.parent() == parent:
                self._value = data._value
            else:
                val = Ps(data)
                self._value = val
        else:
            self._value = data
        self._moments = self._value
        self._parameter = Matrix(parent.base_ring(), 2, 2, parameter)

    def power_series(self):
        ans = self._value.integral().exp()
        return self.parent().power_series_ring()(ans)

    def __call__(self, D):
        return self.evaluate(D)

    def evaluate(self, D):  # meromorphic functions
        K = self.parent().base_ring()

        a, b, c, d = self._parameter.list()
        phi = eval_pseries_map(a, b, c, d)
        try:
            pt = phi(self.normalize_point)
            pole = -d / c
            valinf = evalpoly(self.power_series().list(), pt) * (
                self.normalize_point - pole
            )
        except AttributeError:
            pt = a / c
            pole = None
            valinf = evalpoly(self.power_series().list(), pt)
        if isinstance(D.parent(), Divisors):
            return prod(
                (
                    evalpoly(self.power_series().list(), phi(P))
                    / valinf
                    * ((P - pole) if pole is not None else 1)
                )
                ** n
                for P, n in D
            )
        else:
            return (
                evalpoly(self.power_series().list(), phi(D))
                / valinf
                * ((D - pole) if pole is not None else 1)
            )

    def eval_derivative(self, D):
        if isinstance(D.parent(), Divisors):
            raise NotImplementedError
        K = self.parent().base_ring()
        a, b, c, d = self._parameter.list()
        phi = eval_pseries_map(a, b, c, d)

        valder = self.power_series().derivative().list()
        try:
            pt = phi(self.normalize_point)
            pole = -d / c
            valinf = evalpoly(self.power_series().list(), pt) * (
                self.normalize_point - pole
            )
        except AttributeError:
            pt = a / c
            pole = None
            valinf = evalpoly(self.power_series().list(), pt)
        chainrule = (a * d - b * c) / (c * D + d)
        return (
            evalpoly(valder, phi(D))
            * chainrule
            / valinf
            * ((D - pole) if pole is not None else 1)
        )

    def _cmp_(self, right):
        a = self.power_series()
        b = right.power_series()
        return (a > b) - (a < b)

    def __nonzero__(self):
        return not self._value == 0

    def valuation(self, p=None):
        K = self.parent().base_ring()
        val = self.power_series().list()
        a = (val[0] - 1).valuation(p)
        b = min([o.valuation(p) for o in val[1:]])
        return min(a, b)

    def _add_(self, right):
        if self._parameter != right._parameter:
            raise RuntimeError("Trying to add incompatible series")
        prec = self.parent()._prec
        ans = self._value + right._value
        return self.__class__(self.parent(), ans, self._parameter, check=False)

    def _sub_(self, right):
        if self._parameter != right._parameter:
            raise RuntimeError("Trying to subtract incompatible series")
        prec = self.parent()._prec
        ans = self._value - right._value
        return self.__class__(self.parent(), ans, self._parameter, check=False)

    def _neg_(self):
        prec = self.parent()._prec
        ans = -self._value
        return self.__class__(self.parent(), ans, self._parameter, check=False)

    def scale_by(self, k):  # multiplicative!
        ans = k * self._value
        return self.__class__(self.parent(), ans, self._parameter, check=False)

    def _repr_(self):
        ps = self.parent().power_series_ring()
        return repr(ps(self._value))

    def _acted_upon_(self, g, on_left):
        assert not on_left
        if isinstance(g, Integer):
            return self.scale_by(g)
        else:
            return self.left_act_by_matrix(g)

    def left_act_by_matrix(self, g, param=None):  # meromorphic functions
        Ps = self.parent().power_series_ring()
        K = self.parent().base_ring()
        prec = self.parent()._prec
        p = self.parent()._p
        # Below we code the action which is compatible with the usual action
        # P |-> (aP+b)/(cP+D)
        zz_ps_vec, fact = self.parent().get_action_data(g, self._parameter, param)
        vl = self._value.list()
        ans = [0 for j in range(prec + 1)]
        for i, a in enumerate(vl):
            for j, zij in enumerate(zz_ps_vec[i]):
                ans[j] += a * zij
        ans = (fact * Ps(ans)).add_bigoh(prec)
        return MeromorphicFunctions(K, p=p, prec=prec)(ans, param, check=False)


def eval_pseries_map(a, b, c, d):
    return lambda Q: (Q.parent()(a) * Q + Q.parent()(b)) / (
        Q.parent()(c) * Q + Q.parent()(d)
    )


def divisor_to_pseries(parameter, t):
    a, b, c, d = parameter.list()
    return (
        lambda Q: (
            1
            - (Q.parent()(c) * Q + Q.parent()(d))
            * t
            / (Q.parent()(a) * Q + Q.parent()(b))
        )
        .log()
        .derivative()
    )


class MeromorphicFunctions(Parent, UniqueRepresentation):
    r"""
    TESTS:

    """

    Element = MeromorphicFunctionsElement

    @staticmethod
    def __classcall__(cls, K, p, prec, **kwargs):
        return super().__classcall__(cls, K, p, prec)

    def __init__(self, K, p, prec):
        Parent.__init__(self)
        if prec is None:
            self._prec = K.precision_cap()
        else:
            self._prec = prec

        self._p = p
        self._prec = prec
        self._base_ring = K
        psprec = self._prec
        self._Ps = PowerSeriesRing(self._base_ring, names="t", default_prec=psprec)
        self.V = K ** (prec + 1)

    def prime(self):
        return self._p

    @cached_method
    def get_action_data(self, g, oldparam, param, prec=None):
        if prec is None:
            prec = self._prec
        a, b, c, d = (oldparam * (param * g).adjugate()).list()
        den = self._Ps([d, c]) ** -1
        zz = (self._Ps([b, a]) * den).truncate(prec)
        zzpows = [self._Ps(1), zz]
        for _ in range(prec):
            zzpows.append((zzpows[-1] * zz).truncate(prec))
        fact = den**2
        return zzpows, fact

    def base_ring(self):
        return self._base_ring

    def power_series_ring(self):
        return self._Ps

    def _element_constructor_(self, data, param, check=True):
        return self.element_class(self, data, param, check=check)

    def _repr_(self):
        return (
            "Meromorphic Multiplicative Functions over %s with parameter %s, p = %s and prec = %s"
            % (self._base_ring, self._parameter, self._p, self._prec)
        )
