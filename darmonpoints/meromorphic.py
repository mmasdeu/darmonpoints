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
from .util import muted

def evalpoly(poly, x, check=True):
    # Initialize result
    if len(poly) == 0:
        return 0
    K = (poly[0].parent()(1) * x.parent()(1)).parent()
    x = K(x)
    poly = [K(a) for a in poly]
    if check:
        assert x.valuation() >= 0
    try:
        result = poly[-1]
    except IndexError:
        return x.parent()(0)
    # Evaluate value of polynomial
    # using Horner's method
    for a in reversed(poly):
        result *= x
        result += a
    return result


class MeromorphicFunctionsElement(ModuleElement):
    def __init__(self, parent, data, parameter, check=True):
        ModuleElement.__init__(self, parent)
        prec = parent._prec
        if check:
            K = parent.base_ring()
            Ps = parent._Ps
            if isinstance(data.parent(), Divisors):
                self._value = divisor_to_pseries(parameter, Ps, data, prec).list()
                assert len(data.support()) > 1
            elif data == 0:
                self._value = Ps(1).list()  # multiplicative!
            elif data.parent() == parent:
                self._value = data._value
            else:
                val = Ps(data)
                val /= val[0]
                self._value = val.add_bigoh(prec).list()
        else:
            self._value = data
        self._moments = self._value
        self._value = [o.add_bigoh(prec) for o in self._value]
        while len(self._value) < prec:
            self._value.append(0)
        r = self._value[0]
        if r != 1:
            rinv = ~r
            self._value = [rinv * o for o in self._value]
        self._value = vector(self._value)
        self._parameter = Matrix(parent.base_ring(), 2, 2, parameter)

    def power_series(self):
        return self.parent().power_series_ring()(list(self._value))

    def __call__(self, D):
        return self.evaluate(D)

    # def polynomial_approximation(self, z, m):
    #     K = self.parent().base_ring()
    #     a, b, c, d = self._parameter.list()
    #     phi = lambda Q: a / c if Q == Infinity else (a * Q + b) / (c * Q + d)
    #     try:
    #         _ = phi(self.normalize_point)
    #         pole = -d / c
    #     except AttributeError:
    #         pole = None
    #     valinf = 1
    #     assert pole is None
    #     fac = (z - pole) if pole is not None else 1
    #     phiz = phi(z)
    #     ans = fac * (sum(a*phiz**n for n, a in enumerate(self._value[:m]))) / valinf
    #     return ans

    def evaluate(self, D):  # meromorphic functions
        K = self.parent().base_ring()
        if type(D) in (int, Integer):
            D = K(D)
        a, b, c, d = self._parameter.list()
        phi = lambda Q: a / c if Q == Infinity else (a * Q + b) / (c * Q + d)
        if isinstance(D.parent(), Divisors):
            return prod(evalpoly(self._value, phi(P)) ** n for P, n in D)
        else:
            return evalpoly(self._value, phi(D))

    def eval_derivative(self, D, return_value=False):
        K = self.parent().base_ring()
        if type(D) in (int, Integer):
            D = K(D)
        if isinstance(D.parent(), Divisors):
            raise NotImplementedError
        K = self.parent().base_ring()
        a, b, c, d = self._parameter.list()
        phi = lambda Q: a / c if Q == Infinity else (a * Q + b) / (c * Q + d)
        phiD = phi(D)
        if return_value:
            val = evalpoly(self._value, phiD)
        
        valder = self.power_series().derivative().list()
        chainrule = (a * d - b * c) / (c * D + d) ** 2
        ans = (
            evalpoly(valder, phiD)
            * chainrule
        )
        if return_value:
            return ans, val
        else:
            return ans

    def eval_dlog(self, D):
        K = self.parent().base_ring()
        if type(D) in (int, Integer):
            D = K(D)
        if isinstance(D.parent(), Divisors):
            raise NotImplementedError
        a, b, c, d = self._parameter.list()
        phi = lambda Q: a / c if Q == Infinity else (a * Q + b) / (c * Q + d)
        phiD = phi(D)        
        valder = self.power_series().log().derivative().list()
        chainrule = (a * d - b * c) / (c * D + d) ** 2
        return chainrule * evalpoly(valder, phiD)

    def _cmp_(self, right):
        a = self.power_series()
        b = right.power_series()
        return (a > b) - (a < b)

    def __nonzero__(self):
        return not (self._value[0] == 1 and all(o == 0 for o in self._value[1:]))

    def valuation(self, p=None):
        K = self.parent().base_ring()
        a = (self._value[0] - 1).valuation(p)
        b = min([o.valuation(p) for o in self._value[1:]])
        return min(a, b)

    def _add_(self, right):  # multiplicative!
        if self._parameter != right._parameter:
            raise RuntimeError("Trying to add incompatible series")
        prec = self.parent()._prec
        ans = (self.power_series() * right.power_series()).list()[:prec]
        return self.__class__(self.parent(), ans, self._parameter, check=False)

    def _sub_(self, right):  # multiplicative!
        if self._parameter != right._parameter:
            raise RuntimeError("Trying to subtract incompatible series")
        prec = self.parent()._prec
        ans = (self.power_series() / right.power_series()).list()[:prec]
        return self.__class__(self.parent(), ans, self._parameter, check=False)

    def _neg_(self):  # multiplicative!
        prec = self.parent()._prec
        ans = (~self.power_series()).list()[:prec]
        return self.__class__(self.parent(), ans, self._parameter, check=False)

    def scale_by(self, k):  # multiplicative!
        prec = self.parent()._prec
        ans = (self.power_series() ** k).list()[:prec]
        return self.__class__(self.parent(), ans, self._parameter, check=False)

    def _repr_(self):
        return repr(self.power_series())

    def _acted_upon_(self, g, on_left):
        assert not on_left
        if isinstance(g, Integer):
            return self.scale_by(g)
        else:
            return self.left_act_by_matrix(g)

    def fast_act(self, key):
        zz_ps_vec, param = key
        return self.__class__(
            self.parent(), self._value * zz_ps_vec, param, check=False
        )

    def left_act_by_matrix(self, g, param=None):  # meromorphic functions
        parent = self.parent()
        # Below we code the action which is compatible with the usual action
        # P |-> (aP+b)/(cP+D)
        zz_ps_vec = parent.get_action_data(g, self._parameter, param)
        ans = self._value * zz_ps_vec
        return self.__class__(parent, ans, param, check=False)


def divisor_to_pseries(parameter, Ps, data, prec):
    t = Ps.gen()
    a, b, c, d = parameter.list()
    num = Ps(1).truncate(prec)
    den = Ps(1).truncate(prec)
    for Q, n in data:
        K = Q.parent()
        if n > 0:
            num *= (1 - ((c * Q + d) / (a * Q + b)) * t) ** ZZ(n)
        else:
            den *= (1 - ((c * Q + d) / (a * Q + b)) * t) ** ZZ(-n)
    ans = Ps(num).add_bigoh(prec) * ~(Ps(den).add_bigoh(prec))
    return ans


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
    @muted
    def get_action_data(self, g, oldparam, param, prec=None):
        r'''
        Act on the power series by matrix g, given the old and new parameters.
        The action is given by the formula:
        (g * phi)(t) = phi(tau_0 g^-1 * tau_1^-1 t)
        which amounts to acting on the left by
        tau_1 g tau_0^-1
        '''
        g.set_immutable()
        K = self.base_ring()
        if prec is None:
            prec = self._prec
        assert param is not None
        tg = param.change_ring(K)
        # abcd = tau_0 g^-1 * tau_1^-1
        a, b, c, d = (oldparam * (tg * g).adjugate()).list()
        zz = (
            (self._Ps([b, a]) / self._Ps([d, c]))
            .map_coefficients(lambda x: x.add_bigoh(prec))
            .truncate(prec)
        ) # zz = (at + b)/(ct + d)
        ans = [zz.parent()(1), zz]
        while len(ans) < prec:  # DEBUG - was prec + 1
            zz_ps = (
                (zz * ans[-1])
                .map_coefficients(lambda x: x.add_bigoh(prec))
                .truncate(prec)  # DEBUG - was prec + 1
            )
            ans.append(zz_ps)
        m = Matrix(K, prec, prec, 0)
        for i, zz_ps in enumerate(ans):
            for j, aij in enumerate(zz_ps):
                m[i, j] = aij  # i, j entry contains j-th term of zz^i
        return m

    def base_ring(self):
        return self._base_ring

    def power_series_ring(self):
        return self._Ps

    def _element_constructor_(self, data, param, check=True):
        return self.element_class(self, data, param, check=check)

    def _repr_(self):
        return (
            "Meromorphic Multiplicative Functions over %s with p = %s and prec = %s"
            % (self._base_ring, self._p, self._prec)
        )
