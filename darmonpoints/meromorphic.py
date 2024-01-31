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
                self._value = Ps(1)
                for Q, n in data:
                    self._value *= phi(K(Q)) ** n
                self._value /= self._value[0]
                if len(data.support()) == 1:
                    self.normalize_point = Q + 1  # DEBUG
            elif data == 0:
                self._value = Ps(1)  # multiplicative!
            elif data.parent() == parent:
                self._value = deepcopy(data._value)
            else:
                val = Ps(data)
                val /= val[0]
                self._value = val.add_bigoh(prec)
        else:
            self._value = deepcopy(data)
        self._moments = self._value
        self._parameter = Matrix(parent.base_ring(), 2, 2, parameter)

    def power_series(self):
        return self.parent().power_series_ring()(self._value)

    def __call__(self, D):
        return self.evaluate(D)

    def evaluate(self, D):  # meromorphic functions
        K = self.parent().base_ring()
        phi = eval_pseries_map(self._parameter)
        poly = self._value.polynomial()
        a, b, c, d = self._parameter.list()
        try:
            pt = phi(self.normalize_point)
            pole = -d / c
            valinf = poly(pt) * (self.normalize_point - pole)
        except AttributeError:
            pt = a / c
            pole = None
            valinf = poly(pt)
        if isinstance(D.parent(), Divisors):
            return prod(
                (poly(phi(P)) / valinf * ((P - pole) if pole is not None else 1)) ** n
                for P, n in D
            )
        else:
            return poly(phi(D)) / valinf * ((D - pole) if pole is not None else 1)

    def _cmp_(self, right):
        return (self._value > right._value) - (self._value < right._value)

    def __nonzero__(self):
        return self._value != 1

    def valuation(self, p=None):
        K = self.parent().base_ring()
        return min(
            [Infinity] + [o.valuation(p) for o in (self._value - 1).coefficients()]
        )

    def _add_(self, right):  # multiplicative!
        ans = self._value * right._value
        if self._parameter != right._parameter:
            raise RuntimeError("Trying to add incompatible series")
        return self.__class__(self.parent(), ans, self._parameter, check=False)

    def _sub_(self, right):  # multiplicative!
        ans = self._value / right._value
        if self._parameter != right._parameter:
            raise RuntimeError("Trying to subtract incompatible series")
        return self.__class__(self.parent(), ans, self._parameter, check=False)

    def _neg_(self):  # multiplicative!
        ans = self._value**-1
        return self.__class__(self.parent(), ans, self._parameter, check=False)

    def scale_by(self, k):  # multiplicative!
        ans = self._value**k
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
        Ps = self._value.parent()
        K = self.parent().base_ring()
        prec = self.parent()._prec
        p = self.parent()._p
        # Below we code the action which is compatible with the usual action
        # P |-> (aP+b)/(cP+D)
        # radius = tuple((ky, val) for ky, val in self.parent().radius.items())
        zz_ps_vec = self.parent().get_action_data(g, self._parameter, param)
        poly = self._value.polynomial()
        ans = sum(
            a * zz_ps_vec[e] for a, e in zip(poly.coefficients(), poly.exponents())
        )
        ans /= ans[0]  # always normalize
        ans = ans.add_bigoh(prec)
        return MeromorphicFunctions(K, p=p, prec=prec)(ans, param)


def eval_pseries_map(parameter):
    a, b, c, d = parameter.list()
    return lambda Q: (Q.parent()(a) * Q + Q.parent()(b)) / (
        Q.parent()(c) * Q + Q.parent()(d)
    )


def divisor_to_pseries(parameter, t):
    a, b, c, d = parameter.list()
    return lambda Q: 1 - (Q.parent()(c) * Q + Q.parent()(d)) * t / (
        Q.parent()(a) * Q + Q.parent()(b)
    )


class MeromorphicFunctions(Parent, UniqueRepresentation):
    r"""
    TESTS:

    """
    Element = MeromorphicFunctionsElement

    @staticmethod
    def __classcall__(cls, K, p, prec, **kwargs):
        # radius = kwargs.pop('radius', None)
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
    def get_action_data(self, g, oldparam, param, prec=None):
        verb_level = get_verbose()
        set_verbose(0)
        g.set_immutable()
        K = self.base_ring()
        if prec is None:
            prec = self._prec
        assert param is not None
        tg = param.change_ring(K)
        a, b, c, d = (oldparam * (tg * g).adjugate()).list()
        zz = (self._Ps([b, a]) / self._Ps([d, c])).truncate(prec)
        Ps = self._Ps
        ans = [Ps(1), zz]
        for _ in range(prec - 1):
            zz_ps = (zz * ans[-1]).truncate(prec + 1)
            ans.append(zz_ps)
        set_verbose(verb_level)
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
