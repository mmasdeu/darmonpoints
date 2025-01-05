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
from sage.misc.timing import cputime
from sage.misc.cachefunc import cached_function, cached_method
from sage.misc.misc_c import prod
from sage.misc.verbose import get_verbose, set_verbose, verbose
from sage.modules.free_module_element import FreeModuleElement_generic_dense
from sage.modules.free_module_element import free_module_element as vector
from sage.modules.module import Module
from sage.modules.vector_integer_dense import Vector_integer_dense
from sage.rings.integer import Integer
from sage.rings.finite_rings.integer_mod_ring import Zmod
from sage.rings.infinity import Infinity
from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import Zp, ZpCA
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
    for a in reversed(poly.list()):
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
                a, b, c, d = parameter.list()
                # phi = divisor_to_pseries(parameter, Ps.gen())
                t = Ps.gen()
                num = Ps(1)
                den = Ps(1)
                for Q, n in data:
                    v = (c * Q + d) / (a * Q + b)
                    if n > 0:
                        num *= (1 - v * t) ** (+n)
                    else:
                        den *= (1 - v * t) ** (-n)
                self._value = num / den
                if len(data.support()) == 1:
                    self.normalize_point = Q + 1  # DEBUG
            elif data == 0:
                self._value = Ps(1)
            elif data.parent() == parent:
                self._value = data._value
            else:
                val = Ps(data)
                val /= val[0]
                self._value = val
        else:
            self._value = data
        assert self._value[0] == 1
        self._moments = self._value
        self._parameter = Matrix(parent.base_ring(), 2, 2, parameter)

    def power_series(self):
        ps = self.parent().power_series_ring()
        return ps(self._value)

    def __call__(self, D):
        return self.evaluate(D)

    def evaluate(self, D):  # meromorphic functions
        K = self.parent().base_ring()

        a, b, c, d = self._parameter.list()
        phi = eval_pseries_map(a, b, c, d)
        try:
            pt = phi(self.normalize_point)
            pole = -d / c
            valinf = evalpoly(self._value, pt) * (self.normalize_point - pole)
        except AttributeError:
            pt = a / c
            pole = None
            valinf = evalpoly(self._value, pt)
        if isinstance(D.parent(), Divisors):
            return prod(
                (
                    evalpoly(self._value, phi(P))
                    / valinf
                    * ((P - pole) if pole is not None else 1)
                )
                ** n
                for P, n in D
            )
        else:
            return (
                evalpoly(self._value, phi(D))
                / valinf
                * ((D - pole) if pole is not None else 1)
            )

    def eval_derivative(self, D):
        if isinstance(D.parent(), Divisors):
            raise NotImplementedError
        K = self.parent().base_ring()
        a, b, c, d = self._parameter.list()
        phi = eval_pseries_map(a, b, c, d)

        valder = self.power_series().derivative()
        try:
            pt = phi(self.normalize_point)
            pole = -d / c
            valinf = evalpoly(self._value, pt) * (self.normalize_point - pole)
        except AttributeError:
            pt = a / c
            pole = None
            valinf = evalpoly(self._value, pt)
        chainrule = (a * d - b * c) / (c * D + d)
        return (
            evalpoly(valder, phi(D))
            * chainrule
            / valinf
            * ((D - pole) if pole is not None else 1)
        )

    def __nonzero__(self):
        return not self.power_series() == 1

    def _add_(self, right):  # multiplicative!
        if self._parameter != right._parameter:
            raise RuntimeError("Trying to add incompatible series")
        ps = self.parent().power_series_ring()
        prec = self.parent()._prec
        ans = (self._value * right._value).add_bigoh(prec)
        return self.__class__(self.parent(), ans, self._parameter, check=False)

    def _sub_(self, right):  # multiplicative!
        if self._parameter != right._parameter:
            raise RuntimeError("Trying to subtract incompatible series")
        ps = self.parent().power_series_ring()
        prec = self.parent()._prec
        ans = (self._value / right._value).add_bigoh(prec)
        return self.__class__(self.parent(), ans, self._parameter, check=False)

    def _neg_(self):  # multiplicative!
        ps = self.parent().power_series_ring()
        prec = self.parent()._prec
        ans = ~self._value
        return self.__class__(self.parent(), ans, self._parameter, check=False)

    def scale_by(self, k):  # multiplicative!
        prec = self.parent()._prec
        ans = (self._value**k).add_bigoh(prec)
        return self.__class__(self.parent(), ans, self._parameter, check=False)

    def _repr_(self):
        return repr(self._value)

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
        tmp = param * g
        tmp = Matrix([[tmp[1, 1], -tmp[0, 1]], [-tmp[1, 0], tmp[0, 0]]])  # adjugate
        a, b, c, d = (self._parameter * tmp).list()
        zz_ps_vec = self.parent().get_action_data(a, b, c, d, prec)
        vl = self._value
        ps = self.parent().power_series_ring()
        ans = [0 for j in range(prec + 1)]
        for a, f in zip(vl, zz_ps_vec):
            for j, zij in enumerate(f):
                ans[j] += a * zij
        r = ans[0]
        ans = ps([o / r for o in ans])
        return MeromorphicFunctions(K, p=p, prec=prec)(ans, param, check=False)


def eval_pseries_map(a, b, c, d):
    return lambda Q: (Q.parent()(a) * Q + Q.parent()(b)) / (
        Q.parent()(c) * Q + Q.parent()(d)
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

    def prime(self):
        return self._p

    @cached_method
    def get_action_data(self, a, b, c, d, prec):
        r = -c / d
        rpow = 1
        rlist = [1, r]
        for j in range(prec):
            rlist.append(rlist[-1] * r)
        rlist.append(0)
        slist = [(b * rlist[i] + a * rlist[i + 1]) / d for i in range(len(rlist) - 1)]
        zz = self._Ps(slist)
        zzpow = 1
        ans = [[1]]
        for j in range(prec):
            zzpow = (zzpow * zz).add_bigoh(prec)
            ans.append(zzpow)
        return ans

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
