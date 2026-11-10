#########################################################################
#       Copyright (C) 2011 Cameron Franc and Marc Masdeu
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#                  http://www.gnu.org/licenses/
#########################################################################
from copy import deepcopy

from sage.categories.pushout import pushout
from sage.functions.log import log as _log
from sage.matrix.constructor import Matrix, matrix
from sage.matrix.matrix_space import MatrixSpace
from sage.misc.timing import cputime
from sage.misc.cachefunc import cached_function, cached_method
from sage.misc.lazy_attribute import lazy_attribute
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
from sage.structure.sage_object import SageObject, load, save
from sage.structure.unique_representation import (
    CachedRepresentation,
    UniqueRepresentation,
)
from itertools import islice

from .divisors import Divisors, DivisorsElement
from .util import muted, set_immutable, speed_up_padic_inversion

def evalpoly(poly, x, prec=None, check=True):
    if prec is None:
        prec = len(poly)
    # Initialize result
    if len(poly) == 0:
        return 0
    # Keep the low-degree terms t^0, ..., t^{prec-1} (matches the semantics
    # of the old call site `evalpoly(self._value[:prec], ...)`).
    poly = poly[:prec]
    K = x.parent()
    P0 = poly[0].parent()
    if P0 is not K:
        K = (P0(1) * K(1)).parent()
        x = K(x)
    # Coercing coefficients that already lie in K is not free (it goes through
    # the generic element constructor) and dominated the cost of evaluation.
    if P0 is not K or any(a.parent() is not K for a in poly):
        poly = [K(a) for a in poly]
    if check:
        assert x.valuation() >= 0
    # Evaluate value of polynomial using Horner's method:
    # result starts at 0 and we fold in poly[-1], poly[-2], ..., poly[0].
    # (Seeding result with a coefficient and then also including that same
    # coefficient in the loop double-counts it and adds a spurious
    # poly[-1] * x**len(poly) term -- that was the previous bug here.)
    result = K(0)
    for a in reversed(poly):
        result *= x
        result += a
    return result


class MeromorphicFunctionsElement(ModuleElement):
    def __init__(self, parent, data, parameter=None, check=True):
        if parameter is None:
            parameter = Matrix(parent.base_ring(), 2, 2, [1, 0, 0, 1])
        ModuleElement.__init__(self, parent)
        prec = parent._prec
        if check:
            K = parent.base_ring()
            Ps = parent._Ps
            self._value = None
            if data == 0:
                self._value = Ps(1).list() # multiplicative!
            elif hasattr(data, "parent"):
                if isinstance(data.parent(), Divisors):
                    self._value = divisor_to_pseries(parameter, Ps, data, prec).list()
                    # assert len(data.support()) > 1
                elif data.parent() == parent:
                    self._value = data._value
                elif isinstance(data.parent(), MeromorphicFunctions):
                    self._value = vector(list(data._value.apply_map(lambda x:x.lift_to_precision())))
            if self._value is None:
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

    def evaluate(self, D, prec = None):  # meromorphic functions
        K = self.parent().base_ring()
        if type(D) in (int, Integer):
            D = K(D)
        a, b, c, d = self._parameter.list()
        phi = lambda Q: a / c if Q == Infinity else (a * Q + b) / (c * Q + d)
        if isinstance(D.parent(), Divisors):
            return prod(evalpoly(self._value, phi(P), prec=prec) ** n for P, n in D)
        else:
            return evalpoly(self._value, phi(D), prec=prec)

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
        
        valder = self._derivative_coeffs()
        chainrule = (a * d - b * c) / (c * D + d) ** 2
        ans = (
            evalpoly(valder, phiD)
            * chainrule
        )
        if return_value:
            return ans, val
        else:
            return ans

    @cached_method
    def _derivative_coeffs(self):
        return self.power_series().derivative().list()

    @cached_method
    def _dlog_coeffs(self):
        return self.power_series().log().derivative().list()

    def eval_dlog(self, D):
        K = self.parent().base_ring()
        if type(D) in (int, Integer):
            D = K(D)
        if isinstance(D.parent(), Divisors):
            raise NotImplementedError
        a, b, c, d = self._parameter.list()
        phi = lambda Q: a / c if Q == Infinity else (a * Q + b) / (c * Q + d)
        phiD = phi(D)
        # The coefficients of (log F)' do not depend on D: computing them (a power
        # series logarithm) dominated the cost of each call, so cache them.
        valder = self._dlog_coeffs()
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
        # assert not on_left
        if isinstance(g, Integer):
            return self.scale_by(g)
        else:
            return self.left_act_by_matrix(g)

    def fast_act(self, key):
        zz_ps_vec, param = key
        return self.__class__(
            self.parent(), self._value * zz_ps_vec, param, check=False
        )

    def left_act_by_matrix(self, g, param=None, fast=True):  # meromorphic functions
        if param is None:
            param = self._parameter
        parent = self.parent()
        # Below we code the action which is compatible with the usual action
        # P |-> (aP+b)/(cP+D)
        if fast:
            zz_ps_vec = parent.get_action_data(g, self._parameter, param)
            ans = self._value * zz_ps_vec
            return self.__class__(parent, ans, param, check=False)
        else:
            set_immutable(g)
            assert g.parent() == MatrixSpace(parent.base_ring(), 2, 2), g.parent()
            K = parent.base_ring()
            prec = parent._prec
            assert param is not None
            tg = param.change_ring(K)
            # abcd = tau_0 g^-1 * tau_1^-1
            a, b, c, d = (self._parameter * (tg * g).adjugate()).list()
            zz = (
                (parent._Ps([b, a]) / parent._Ps([d, c]))
                .truncate(prec)
                .map_coefficients(lambda x: x.add_bigoh(prec+1))
                
            )
            return self.__class__(parent, evalpoly(self._value, zz), param, check=False)


def divisor_to_pseries(parameter, Ps, data, prec):
    t = Ps.gen()
    a, b, c, d = parameter.list()
    num = Ps(1).truncate(prec)
    den = Ps(1).truncate(prec)
    for Q, n in data:
        K = Q.parent()
        if n > 0:
            num *= (1 - ((c * Q + d) / (a * Q + b)) * t) ** ZZ(n)
            num = num.add_bigoh(prec)
        else:
            den *= (1 - ((c * Q + d) / (a * Q + b)) * t) ** ZZ(-n)
            den = den.add_bigoh(prec)
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
        speed_up_padic_inversion(K)
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
        r'''
        Act on the power series by matrix g, given the old and new parameters.
        The action is given by the formula:
        (g * phi)(t) = phi(tau_0 g^-1 * tau_1^-1 t)
        which amounts to acting on the left by
        tau_1 g tau_0^-1
        '''
        return self.compute_action_data(g, oldparam, param, prec)

    @muted
    def compute_action_data(self, g, oldparam, param, prec=None):
        r'''
        Uncached version of get_action_data. Looking up the cache of
        get_action_data needs hashing p-adic matrices, which is slow, so
        callers that do their own caching should use this one.
        '''
        K = self.base_ring()
        if prec is None:
            prec = self._prec
        assert param is not None
        tg = param.change_ring(K)
        if not hasattr(g, 'adjugate'):
            g = g.matrix().change_ring(K)

        # abcd = tau_0 g^-1 * tau_1^-1
        a, b, c, d = (oldparam * (tg * g).adjugate()).list()
        if not d.is_zero() and (c / d).valuation() >= 0:
            return self._action_matrix_moebius(a, b, c, d, prec)
        zz = (
            (self._Ps([b, a]) / self._Ps([d, c]))
            .truncate(prec)
            .map_coefficients(lambda x: x.add_bigoh(prec+1))
        ) # zz = (at + b)/(ct + d)
        ans = [zz.parent()(1), zz]
        while len(ans) < prec:
            zz_ps = (
                (zz * ans[-1])
                .truncate(prec)
                .map_coefficients(lambda x: x.add_bigoh(prec+1))
            )
            ans.append(zz_ps)
        m = Matrix(K, prec, prec, 0)
        for i, zz_ps in enumerate(ans):
            for j, aij in enumerate(zz_ps):
                m[i, j] = aij  # i, j entry contains j-th term of zz^i
        return m

    def _action_matrix_moebius(self, a, b, c, d, prec):
        r'''
        Same matrix as in get_action_data (row i contains the coefficients of
        zz^i, where zz = (at + b)/(ct + d)), computed using that
        zz^i = zz^(i-1) * (b1 + a1 t) / (1 + c1 t). This only needs O(prec)
        operations per row instead of a product of power series.

        Assumes that c/d has nonnegative valuation, so that the division by
        1 + c1 t does not lose precision.
        '''
        K = self.base_ring()
        dinv = ~d
        a1, b1, c1 = a * dinv, b * dinv, c * dinv
        bound = prec + 1
        zero = K(0)
        m = Matrix(K, prec, prec, 0)
        m[0, 0] = 1
        w = [K(1)] + [zero] * (prec - 1)
        for i in range(1, prec):
            u = []
            prev_w = zero
            prev_u = zero
            for k in range(prec):
                wk = w[k]
                uk = b1 * wk + a1 * prev_w - c1 * prev_u
                if not uk._is_exact_zero():
                    uk = uk.add_bigoh(bound)
                prev_w = wk
                prev_u = uk
                u.append(uk)
            # Like the coefficients of a polynomial, drop the trailing zeros
            # (they are left as exact zeros in the matrix)
            n = prec
            while n > 0 and u[n - 1].is_zero():
                n -= 1
            if n == 0:
                break # All the remaining powers vanish
            for j in range(n):
                m[i, j] = u[j]
            w = u
        return m

    def base_ring(self):
        return self._base_ring

    def power_series_ring(self):
        return self._Ps

    def _element_constructor_(self, data, param=None, check=True):
        if param is None:
            param = Matrix(self.base_ring(), 2, 2, [1, 0, 0, 1])
        return self.element_class(self, data, parameter=param, check=check)

    def _repr_(self):
        return (
            "Meromorphic Multiplicative Functions over %s with p = %s and prec = %s"
            % (self._base_ring, self._p, self._prec)
        )


#########################################################################
# Additive implementation
#
# When the functions are principal units, we store log F instead of F, so
# that products become sums (see AdditiveMeromorphicFunctions), and compute
# linear combinations of their translates by matrices with integer matrices
# (see LogSeriesOperator). This is used by ThetaOCAdditive and by the
# Darmon-Vonk cocycles.
#########################################################################


def _to_integer(x, pN):
    r'''
    An integer congruent to the p-adic integer x modulo pN.
    '''
    return ZZ(0) if x.is_zero() else ZZ(x.lift()) % pN


def _reduce_columns(R, mods):
    return [[int(R[b, k]) % int(mods[k]) for k in range(R.ncols())] for b in range(R.nrows())]


def _coordinate_moebius_entries(Ra, Rb, Rc, P, mods):
    r'''
    The nonzero entries (r, c, u) of the matrix whose row r contains the
    coefficients of zz^r, where zz = (b1 + a1 t) / (1 + c1 t) is a power series
    over the ring of integers O_K, given in coordinates: u is the list of
    coordinates of the entry, reduced modulo mods (see _OKCoordinates).

    The input are the matrices (as lists of rows) of the multiplication by a1,
    b1 and c1, acting on row vectors of coordinates. The rows are computed with
    zz^r = zz^(r-1) * (b1 + a1 t) / (1 + c1 t), that is, the coefficients satisfy
    u_k = b1 w_k + a1 w_(k-1) - c1 u_(k-1).
    '''
    from operator import mul
    d = len(mods)
    mods = [int(o) for o in mods]
    # Columns of the matrices, to compute the products with sum(map(mul, ...))
    columns = lambda R : [[R[b][k] for b in range(d)] for k in range(d)]
    Ca, Cb, Cc = columns(Ra), columns(Rb), columns(Rc)
    zero = [0] * d
    w = [[1] + [0] * (d - 1)] + [zero] * (P - 1) # zz^0 = 1
    entries = []
    for r in range(1, P):
        u = []
        prev_w = zero
        prev_u = zero
        nonzero = False
        for k in range(P):
            wk = w[k]
            if any(wk) or any(prev_w) or any(prev_u):
                uk = [(sum(map(mul, wk, Cb[j])) + sum(map(mul, prev_w, Ca[j])) - sum(map(mul, prev_u, Cc[j]))) % mods[j]
                      for j in range(d)]
                if any(uk):
                    nonzero = True
                    entries.append((r, k, uk))
            else:
                uk = zero
            u.append(uk)
            prev_w = wk
            prev_u = uk
        if not nonzero:
            break # All the remaining powers vanish
        w = u
    return entries


def _integer_moebius_matrix(a1, b1, c1, P, pN):
    r'''
    The P x P integer matrix whose row r contains the coefficients of zz^r
    modulo pN, where zz = (b1 + a1 t) / (1 + c1 t) (as in
    MeromorphicFunctions._action_matrix_moebius, but with integers).
    '''
    rows = [[1] + [0] * (P - 1)]
    w = rows[0]
    for _ in range(1, P):
        u = []
        prev_w = 0
        prev_u = 0
        for wk in w:
            uk = (b1 * wk + a1 * prev_w - c1 * prev_u) % pN
            prev_w = wk
            prev_u = uk
            u.append(uk)
        if not any(u):
            break # All the remaining powers vanish
        rows.append(u)
        w = u
    rows += [[0] * P for _ in range(P - len(rows))]
    return matrix(ZZ, rows)


def _check_integral(elements):
    if any(o.valuation() < 0 for o in elements if not o.is_zero()):
        raise ValueError('Not integral')


def _coordinates(x, F):
    r'''
    Coordinates of the integral element x of F in the basis given by
    _integral_basis(F).
    '''
    if F.absolute_degree() == 1:
        return [ZZ(0) if x.is_zero() else ZZ(x.lift())]
    if x.is_zero():
        return [ZZ(0)] * F.absolute_degree()
    try:
        # Unramified extensions (FLINT): x = p^v * poly(g)
        poly, v = x._flint_rep_abs()
        if v < 0:
            raise ValueError('Not integral')
        coeffs = poly.list()
        pv = ZZ(F.prime())**v
        return [ZZ(c) * pv for c in coeffs] + [ZZ(0)] * (F.absolute_degree() - len(coeffs))
    except AttributeError:
        pass
    B = F.base_ring()
    try:
        # Relative extensions: the underlying polynomial in the generator,
        # over the (floating point) base ring. Much faster than x.polynomial()
        coeffs = x._poly_rep().list()
    except AttributeError:
        coeffs = x.polynomial().list()
    ans = [c for a in coeffs for c in _coordinates(a, B)]
    return ans + [ZZ(0)] * (F.absolute_degree() - len(ans))


def _from_coordinates(c, F):
    r'''
    Inverse of _coordinates. The element is built from its coefficients (and
    not as a linear combination of the basis), so that it has the best
    precision that F can represent.
    '''
    if F.absolute_degree() == 1:
        return F(ZZ(c[0]))
    B = F.base_ring()
    n = F.relative_degree()
    k = len(c) // n
    gen = F.gen()
    # (F(list) loses precision for absolute Eisenstein extensions)
    return sum((F(_from_coordinates(c[i * k : (i + 1) * k], B)) * gen**i for i in range(n)), F(0))


def _integral_basis(F):
    r'''
    A Z_p-basis of the ring of integers of F: the products gen^i * b, where
    gen is the generator of F over its base ring and b runs over the basis of
    the base ring. For an Eisenstein extension of an unramified extension, it
    is (pi^i * g^j).
    '''
    if F.absolute_degree() == 1:
        return [F(1)]
    gen = F.gen()
    return [gen**i * F(b) for i in range(F.relative_degree()) for b in _integral_basis(F.base_ring())]


class _IntegerOperator(SageObject):
    r'''
    The linear map v |-> v * A on row vectors of integers (given as lists),
    for an integer matrix A whose column c is only needed modulo p^exps[c].

    There are three ways of computing the product:

    - 'dense': with FLINT (Sage's integer matrices).

    - 'sparse': with python integers, from the nonzero entries of A (column by
      column). Much faster than Sage's products when A is sparse.

    - 'banded': write each entry of A, and of v, as p^val times a smaller
      number. The rows and the columns of A are grouped in bands according
      to the valuations of their entries, and each block (row band, column
      band) is stored divided by p^mu, where mu is the smallest valuation of
      its entries, and reduced modulo p^(M - mu) (M being the largest
      exponent of its columns). In the product, the part of v corresponding
      to a row band is also divided by the power of p of its valuation
      beta, so that the block only needs to be computed modulo
      p^(M - mu - beta), with much smaller numbers (and not at all when
      mu + beta >= M). Integers modulo p^N cannot take advantage of the
      valuations of their entries by themselves, but this way the products
      only involve their significant digits.
    '''
    def __init__(self, A, p, exps, d, mode='auto', nbands=8, size=None):
        r'''
        A is either an integer matrix or a dictionary {(r, c) : A[r, c]} of
        its nonzero entries, in which case size = (number of rows, number of
        columns).
        '''
        if isinstance(A, dict):
            self._entries = A
            self._matrix = None
            self.nrows, self.ncols = size
        else:
            self._entries = None
            self._matrix = A
            self.nrows, self.ncols = A.nrows(), A.ncols()
        self.p = ZZ(p)
        self.exps = list(exps)
        if mode == 'auto':
            # In our tests (theta functions with series length 120 and 200),
            # FLINT was the fastest for Qp and the sparse products for all the
            # extensions, also when A is not very sparse. The banded products
            # are faster than the dense ones when the moduli are large, but
            # still slower than the sparse ones: the cost of Sage's products of
            # integer vectors and matrices per entry depends little on the
            # size of the entries.
            mode = 'dense' if d == 1 else 'sparse'
        self.mode = mode
        self.sparse = (mode == 'sparse')
        if mode == 'sparse':
            cols = [([], []) for _ in range(self.ncols)]
            for (r, c), a in sorted(self.entries.items(), key=lambda o : o[0][::-1]):
                cols[c][0].append(r)
                cols[c][1].append(int(a))
            self.cols = cols
        elif mode == 'banded':
            self._init_bands(nbands)

    @lazy_attribute
    def entries(self):
        if self._entries is None:
            self._entries = self._matrix.dict()
        return self._entries

    @lazy_attribute
    def A(self):
        if self._matrix is None:
            self._matrix = matrix(ZZ, self.nrows, self.ncols, self._entries)
        return self._matrix

    def _init_bands(self, nbands):
        p, exps = self.p, self.exps
        n, m = self.nrows, self.ncols
        entries = self.entries
        Mmax = max(exps)
        vals = {}
        rowval = [Infinity] * n
        colval = [Infinity] * m
        for (r, c), a in entries.items():
            v = ZZ(a).valuation(p)
            vals[r, c] = v
            rowval[r] = min(rowval[r], v)
            colval[c] = min(colval[c], v)
        width = max(1, -((-Mmax) // nbands))
        rowband = {r : v // width for r, v in enumerate(rowval) if v is not Infinity}
        colband = {c : v // width for c, v in enumerate(colval) if v is not Infinity}
        self.row_bands = {}
        for r, k in sorted(rowband.items()):
            self.row_bands.setdefault(k, []).append(r)
        self.col_bands = {}
        for c, l in sorted(colband.items()):
            self.col_bands.setdefault(l, []).append(c)
        rowpos = {r : i for rows in self.row_bands.values() for i, r in enumerate(rows)}
        colpos = {c : j for cols in self.col_bands.values() for j, c in enumerate(cols)}
        block_entries = {}
        for (r, c), v in vals.items():
            block_entries.setdefault((rowband[r], colband[c]), []).append((rowpos[r], colpos[c], r, c, v))
        self.col_exps = {l : max(exps[c] for c in cols) for l, cols in self.col_bands.items()}
        self.blocks = []
        for (k, l), ents in sorted(block_entries.items()):
            mu = min(o[4] for o in ents)
            M = self.col_exps[l]
            if mu >= M:
                continue
            pmu = p**mu
            mod = p**(M - mu)
            B = matrix(ZZ, len(self.row_bands[k]), len(self.col_bands[l]),
                       {(i, j) : (ZZ(entries[r, c]) // pmu) % mod for i, j, r, c, _ in ents})
            self.blocks.append((k, l, mu, M, B))

    def apply(self, v):
        if self.mode == 'sparse':
            return [sum([v[r] * a for r, a in zip(rows, vals)]) for rows, vals in self.cols]
        if self.mode == 'dense':
            return [int(o) for o in vector(ZZ, v) * self.A]
        p = self.p
        # The parts of v in each row band, divided by the power of p of their valuation
        chunks = {}
        for k, rows in self.row_bands.items():
            chunk = [v[r] for r in rows]
            nonzero = [o for o in chunk if o]
            if not nonzero:
                continue
            beta = min(ZZ(o).valuation(p) for o in nonzero)
            pb = p**beta
            chunks[k] = (beta, [ZZ(o) // pb for o in chunk])
        acc = {}
        for k, l, mu, M, B in self.blocks:
            try:
                beta, w = chunks[k]
            except KeyError:
                continue
            s = beta + mu
            if s >= M:
                continue
            mod = p**(M - s)
            prod = vector(ZZ, [o % mod for o in w]) * B
            ps = p**s
            try:
                acc[l] += ps * prod
            except KeyError:
                acc[l] = ps * prod
        ans = [0] * self.ncols
        for l, w in acc.items():
            for c, o in zip(self.col_bands[l], w):
                ans[c] = o
        return ans


class _PrecisionTracker(SageObject):
    r'''
    The data needed to keep track of the precision of the coefficients in
    _improve_integral: the nonzero entries of the action matrices, with their
    valuations and precisions. They are only computed when needed (when some
    input is not known to the full precision).
    '''
    def __init__(self, blocks, O, N, min_input_prec):
        # blocks: list of (row offset, column offset, {(r, c) : entry}, precision),
        # where the entries are integers (d = 1) or lists of coordinates
        self._blocks = blocks
        self._O = O
        self._N = int(N)
        self.min_input_prec = int(min(min_input_prec, N))

    @lazy_attribute
    def arrays(self):
        import numpy as np
        O, N = self._O, self._N
        p, e = O.p, int(O.e)
        src, dst, vals, precs = [], [], [], []
        for r0, c0, entries, prec in self._blocks:
            if not entries:
                continue
            positions = np.array(list(entries.keys()), dtype=np.int64)
            src.append(positions[:, 0] + r0)
            dst.append(positions[:, 1] + c0)
            if O.d == 1:
                vals.append(np.array([e * int(ZZ(x).valuation(p)) for x in entries.values()], dtype=np.int64))
            else:
                vals.append(np.array(O.element_valuations([c for u in entries.values() for c in u], N), dtype=np.int64))
            precs.append(np.full(len(entries), int(prec), dtype=np.int64))
        if not src:
            empty = np.zeros(0, dtype=np.int64)
            return empty, empty, empty, empty, empty, empty
        src, dst, vals, precs = [np.concatenate(o) for o in (src, dst, vals, precs)]
        # Sort by target, for np.minimum.reduceat
        order = np.argsort(dst, kind='stable')
        src, dst, vals, precs = src[order], dst[order], vals[order], precs[order]
        targets, starts = np.unique(dst, return_index=True)
        return src, dst, vals, precs, targets, starts


class _OKCoordinates(SageObject):
    r'''
    Coordinates of the elements of the ring of integers O_K of a p-adic field
    K in a Z_p-basis.

    The basis elements (pi^i * g^j) have valuations i, so that the elements of
    pi^N O_K are those whose coordinate (i, j) is divisible by
    p^ceil((N - i) / e). Since all the maps that we use are O_K-linear, we can
    reduce each coordinate modulo its own power of p without losing anything.
    '''
    def __init__(self, K):
        self.K = K
        self.p = ZZ(K.prime())
        self.e = ZZ(K.absolute_e())
        self.basis = _integral_basis(K)
        self.d = len(self.basis)
        self.offsets = [ZZ(b.valuation()) for b in self.basis]
        # For absolute Eisenstein extensions, Sage's x.polynomial() can be wrong
        # in the last digits when the absolute precision of x is larger than
        # the precision cap (as happens for elements of positive valuation).
        # So in that case we compute everything from the Eisenstein polynomial.
        self._absolute_eisenstein = (K.absolute_degree() > 1 and self.e > 1
                                     and K.base_ring().absolute_degree() == 1)
        if self._absolute_eisenstein:
            # Multiplication by pi: pi * pi^b = pi^(b+1), and pi^e = -sum_k f_k pi^k
            e = self.e
            f = [ZZ(c.lift()) for c in K.defining_polynomial().list()]
            Rpi = matrix(ZZ, e, e)
            for b in range(e - 1):
                Rpi[b, b + 1] = 1
            for k in range(e):
                Rpi[e - 1, k] = -f[k]
            self._Rpi_powers = {0 : matrix.identity(ZZ, e), 1 : Rpi}
            # The b-th basis element is pi^b
            self.R = [self._Rpi_power(b) for b in range(e)]
        else:
            # Matrix of the multiplication by the b-th basis element, acting on row vectors
            self.R = [matrix(ZZ, [self.coords(bb * b) for bb in self.basis]) for b in self.basis]

    def _Rpi_power(self, v):
        try:
            return self._Rpi_powers[v]
        except KeyError:
            ans = self._Rpi_powers[v] = self._Rpi_powers[1]**v
            return ans

    @lazy_attribute
    def _kind(self):
        K = self.K
        if K.absolute_degree() == 1:
            return 'Qp'
        if self._absolute_eisenstein:
            return 'absolute eisenstein'
        try:
            if self.e == 1:
                _ = K(1)._flint_rep_abs()
                return 'unramified'
            B = K.base_ring()
            if B.absolute_e() == 1 and B.absolute_degree() > 1:
                _ = K(1)._poly_rep().list()[0]._flint_rep_abs()
                return 'eisenstein over unramified'
        except AttributeError:
            pass
        return 'generic'

    def coords(self, x):
        kind = self._kind
        if x.is_zero():
            return [ZZ(0)] * self.d
        if kind == 'Qp':
            return [ZZ(x.lift())]
        if kind == 'unramified':
            return self._unramified_coords(x, self.d)
        if kind == 'eisenstein over unramified':
            # The underlying polynomial in pi, over the (floating point)
            # unramified ring. Much faster than x.polynomial()
            f = self.d // self.e
            ans = [c for a in x._poly_rep().list() for c in self._unramified_coords(a, f)]
            return ans + [ZZ(0)] * (self.d - len(ans))
        if kind == 'absolute eisenstein':
            v = x.valuation()
            if v > 0:
                # x = pi^v * u, and the precision of the unit u is at most the cap
                return list(vector(ZZ, _coordinates(x.unit_part(), self.K)) * self._Rpi_power(v))
        return _coordinates(x, self.K)

    def _unramified_coords(self, x, f):
        if x.is_zero():
            return [ZZ(0)] * f
        # x = p^v * poly(g)
        poly, v = x._flint_rep_abs()
        if v < 0:
            raise ValueError('Not integral')
        pv = self.p**v
        coeffs = poly.list()
        return [ZZ(c) * pv for c in coeffs] + [ZZ(0)] * (f - len(coeffs))

    def moduli(self, N):
        r'''
        The moduli of the coordinates of the elements of pi^N O_K.
        '''
        return [self.p**max(0, -((o - N) // self.e)) for o in self.offsets]

    def valuation(self, w, N):
        r'''
        Valuation of a vector of coordinates of elements (at most N).
        '''
        p, e, d = self.p, self.e, self.d
        return min([N] + [e * ZZ(c).valuation(p) + self.offsets[k % d] for k, c in enumerate(w) if c != 0])

    def element_valuations(self, w, N):
        r'''
        The valuations (at most N) of the elements whose coordinates are the
        consecutive blocks of d entries of w, as a list of python integers.
        '''
        p, e, d, offsets = self.p, int(self.e), self.d, self.offsets
        N = int(N)
        w = [ZZ(c) for c in w]
        if d == 1:
            return [e * int(c.valuation(p)) if c else N for c in w]
        ans = []
        for k in range(0, len(w), d):
            v = N
            for c, o in zip(w[k : k + d], offsets):
                if c:
                    v = min(v, e * int(c.valuation(p)) + int(o))
            ans.append(v)
        return ans

    def element(self, c, N):
        K = self.K
        kind = self._kind
        c = [ZZ(o) for o in c]
        if kind == 'Qp':
            return K(c[0]).add_bigoh(N)
        if kind == 'unramified':
            return K(c).add_bigoh(N)
        if kind == 'eisenstein over unramified':
            B = K.base_ring()
            f = self.d // self.e
            return K([B(c[i * f : (i + 1) * f]) for i in range(self.e)]).add_bigoh(N)
        return _from_coordinates(c, K).add_bigoh(N)


@cached_function
def _ok_coordinates(K):
    return _OKCoordinates(K)


@cached_function
def _inverse_integers(K, n):
    r'''
    The list [1/1, 1/2, ..., 1/n] of elements of K.
    '''
    return [None] + [K(QQ(1) / k) for k in range(1, n + 1)]


def _ramification_data(K):
    p = K.prime()
    try:
        e = K.absolute_e()
    except AttributeError:
        e = K.ramification_index()
    return p, ZZ(e)


def log_principal(u, prec=None):
    r'''
    Logarithm of a principal unit u (that is, u = 1 mod the maximal ideal),
    computed with the power series of log(1 + y).

    This is much faster than u.log() for extensions of extensions.
    '''
    K = u.parent()
    p, e = _ramification_data(K)
    y = u - 1
    if y.is_zero():
        return K(0).add_bigoh(u.precision_absolute())
    vy = y.valuation()
    if vy <= 0:
        raise ValueError('Not a principal unit')
    if prec is None:
        prec = u.precision_absolute()
    # The k-th term has valuation k * vy - e * v_p(k) >= f(k) = k * vy - e * log_p(k),
    # and f is increasing for k >= e / (vy * ln(p)). Stop when all the
    # remaining terms are negligible.
    lnp = float(_log(p))
    kmax = 1
    while kmax * vy * lnp < e or (kmax + 1) * vy - e * float(_log(kmax + 1)) / lnp < prec:
        kmax += 1
    inv = _inverse_integers(K, kmax)
    # Horner: log(1+y) = y (1 - y (1/2 - y (1/3 - ...)))
    ans = inv[kmax]
    for k in range(kmax - 1, 0, -1):
        ans = inv[k] - y * ans
    return (y * ans).add_bigoh(prec)


def exp_small(s, prec=None):
    r'''
    Exponential of s, which is assumed to have valuation > e / (p - 1).
    '''
    K = s.parent()
    p, e = _ramification_data(K)
    if prec is None:
        prec = min(s.precision_absolute(), K.precision_cap())
    if s.is_zero():
        return K(1).add_bigoh(prec)
    vs = s.valuation()
    if vs * (p - 1) <= e:
        raise ValueError('exp does not converge')
    # The k-th term has valuation k * vs - e * v_p(k!) >= k * vs - e * (k - 1) / (p - 1),
    # which is increasing in k. Stop when all the remaining terms are negligible.
    kmax = 1
    while (kmax + 1) * vs - e * QQ(kmax) / (p - 1) < prec:
        kmax += 1
    inv = _inverse_integers(K, kmax)
    # Horner: exp(s) = 1 + s (1 + s/2 (1 + s/3 (...)))
    ans = K(1)
    for k in range(kmax, 0, -1):
        ans = 1 + s * inv[k] * ans
    return ans.add_bigoh(prec)


def principal_part_log(w, q):
    r'''
    For a unit w, return log of its principal part w / teichmuller(w), computed
    as log(w^(q-1)) / (q-1), which avoids computing the Teichmuller lift.
    '''
    return log_principal(w**(q - 1)) / (q - 1)


class LogSeries(SageObject):
    r'''
    Power series log F(t), where t is the coordinate given by the parameter.
    '''
    def __init__(self, value, parameter):
        self._value = value
        self._parameter = parameter

    def evaluate(self, D, prec=None):
        a, b, c, d = self._parameter.list()
        phi = lambda Q: a / c if Q == Infinity else (a * Q + b) / (c * Q + d)
        if isinstance(D, DivisorsElement):
            return sum(n * evalpoly(self._value, phi(P), prec=prec) for P, n in D)
        else:
            return evalpoly(self._value, phi(D), prec=prec)

    def eval_dlog(self, D):
        r'''
        Logarithmic derivative of the corresponding multiplicative series,
        which here is just the derivative of the log-series.
        '''
        a, b, c, d = self._parameter.list()
        phiD = (a * D + b) / (c * D + d)
        try:
            der = self._der_coeffs
        except AttributeError:
            der = [k * o for k, o in enumerate(self._value)][1:]
            self._der_coeffs = der
        chainrule = (a * d - b * c) / (c * D + d) ** 2
        return chainrule * evalpoly(der, phiD)

    def act(self, action_data):
        r'''
        Log of the result of fast_act on the corresponding multiplicative
        series: compose with the Mobius transformation, and normalize so that
        the value at 0 is 0 (the multiplicative version divides by the value at
        0 instead).
        '''
        M, param = action_data
        ans = self._value * M
        ans[0] = 0
        return LogSeries(ans, param)

    def _repr_(self):
        return f'log-series {self._value}'


def log_series_of_divisor(D, parameter, prec):
    r'''
    log of the power series that MeromorphicFunctions(K, p, prec)(D, parameter)
    represents, namely the sum over (Q, n) in D of n * log(1 - x_Q t), where
    x_Q = (c Q + d) / (a Q + b).
    '''
    K = parameter.base_ring()
    a, b, c, d = parameter.list()
    coeffs = [K(0) for _ in range(prec)]
    for Q, n in D:
        x = c / a if Q == Infinity else (c * Q + d) / (a * Q + b)
        if x.valuation() <= 0:
            raise NotImplementedError('The series is not a principal unit')
        xk = x
        for k in range(1, prec):
            coeffs[k] += n * xk
            xk *= x
    inv = _inverse_integers(K, prec)
    coeffs = [K(0)] + [-inv[k] * coeffs[k] for k in range(1, prec)]
    return vector(K, [o.add_bigoh(prec) for o in coeffs])


def _integral_moebius_coefficients(abcd):
    r'''
    Given the entries (a, b, c, d) of a Mobius transformation
    zz = (a t + b) / (c t + d), return [a1, b1, c1] such that
    zz = (b1 + a1 t) / (1 + c1 t), checking that they are integral (as
    needed by LogSeriesOperator).

    For the action of a matrix g on power series (see
    MeromorphicFunctions.get_action_data), the entries are those of
    oldparam * (param * g).adjugate().
    '''
    a, b, c, d = abcd
    if d.is_zero():
        raise ValueError('d = 0')
    coeffs = [a / d, b / d, c / d]
    _check_integral(coeffs)
    return coeffs


class LogSeriesOperator(SageObject):
    r'''
    A linear map on n-tuples of log-series of length P over K (vectors of
    coefficients of log F, normalized by log F(0) = 0, see LogSeries), of the
    form

        (F_0, ..., F_{n-1}) |-> (G_0, ..., G_{n-1}),

        G_i(t) = sum_j sum_{(m, zz)} m * (F_j(zz(t)) - F_j(zz(0))),

    where the m are integers and zz = (b1 + a1 t) / (1 + c1 t) are Mobius
    transformations with a1, b1 and c1 in the ring of integers O_K. That is, a
    linear combination of the actions of matrices on log-series (see
    MeromorphicFunctions.get_action_data and LogSeries.act).

    It is computed with integer matrices, which is much faster than with
    matrices over K: each element of O_K is replaced by its coordinates in a
    Z_p-basis of O_K (see _OKCoordinates), and the multiplication by an
    element of O_K by an integer matrix. The matrices of the action are
    computed directly in these coordinates, with the recurrence that defines
    the powers of the Mobius transformations, and everything is computed
    modulo pi^P.

    The vectors on which it acts (see to_vector) are the concatenation of the
    coordinates of the coefficients of F_0, ..., F_{n-1}. They do not carry
    the precision of the coefficients, which can be tracked separately (see
    initial_precisions and propagate), as the p-adic elements would.

    INPUT:

    - ``K`` -- a p-adic field

    - ``P`` -- the length of the series

    - ``n`` -- the number of series

    - ``terms`` -- a dictionary {(j, i) : list of (m, [a1, b1, c1])}, where
      a1, b1 and c1 are integral elements of K (see
      _integral_moebius_coefficients)

    - ``mode`` -- how to compute the products with integer matrices (see
      _IntegerOperator)

    TESTS::

        sage: from darmonpoints.meromorphic import AdditiveMeromorphicFunctions, LogSeriesOperator, _integral_moebius_coefficients
        sage: from darmonpoints.divisors import Divisors
        sage: K.<a> = Qq(25, 20)
        sage: A = AdditiveMeromorphicFunctions(K, 5, 20)
        sage: Div = Divisors(K)
        sage: f0 = A(Div([(1, a/5), (-1, (a + 1)/5)]))
        sage: f1 = A(Div([(1, 1/(5*a)), (-1, (a + 2)/25)]))
        sage: g = matrix(K, 2, 2, [1, a, 5, 3])
        sage: h = matrix(K, 2, 2, [2, 1, 5*a, 1])
        sage: coeffs = lambda m : _integral_moebius_coefficients(m.adjugate().list())
        sage: terms = {(0, 0) : [(1, coeffs(g)), (2, coeffs(h))], (1, 0) : [(-1, coeffs(h))], (1, 1) : [(3, coeffs(g * h))]}
        sage: P = A.series_length()
        sage: op = LogSeriesOperator(K, P, 2, terms)
        sage: elts = list(f0._value) + list(f1._value)
        sage: v = op.to_vector(elts)
        sage: precs = op.propagate(op.initial_precisions(elts), v)
        sage: G0, G1 = [A(w, check=False) for w in op.to_values(op.reduce(op.apply(v)), precs)]
        sage: G0 == g * f0 + 2 * (h * f0) - h * f1
        True
        sage: G1 == 3 * (g * (h * f1))
        True
    '''
    def __init__(self, K, P, n, terms, mode='auto'):
        O = _ok_coordinates(K)
        self.K = K
        self.O = O
        self.P = P
        self.n = n
        d = O.d
        N = P
        mods = O.moduli(N)
        # The entries of the action matrices are known to the precision of a1,
        # b1 and c1, since products and sums of integral elements do not lose
        # absolute precision.
        moebius_prec = {}
        for ji, lst in terms.items():
            for _, coeffs in lst:
                _check_integral(coeffs)
            moebius_prec[ji] = min([P + 1] + [o.precision_absolute() for _, coeffs in lst for o in coeffs])
        # Group the terms of each block by their Mobius transformation, given
        # by the coordinates of a1, b1 and c1 modulo pi^N (which is all that
        # the integer matrices depend on), adding up the multiplicities. The
        # matrix of each transformation is computed only once, since they
        # often appear in several blocks.
        key = lambda coeffs : tuple(int(c) % int(md) for o in coeffs for c, md in zip(O.coords(o), mods))
        blocks = {}
        for ji, lst in terms.items():
            grouped = {}
            for m, coeffs in lst:
                k = key(coeffs)
                try:
                    grouped[k][0] += int(m)
                except KeyError:
                    grouped[k] = [int(m), coeffs]
            blocks[ji] = [(m, k, coeffs) for k, (m, coeffs) in grouped.items() if m]
        cache = {}
        # For the precision tracking: the nonzero entries of the action
        # matrices, as (row offset, column offset, entries, precision) for each block
        track = []
        if d == 1:
            pN = mods[0]
            A = matrix(ZZ, n * P, n * P)
            for (j, i), lst in blocks.items():
                M = matrix(ZZ, P, P)
                for m, k, coeffs in lst:
                    try:
                        Mk = cache[k]
                    except KeyError:
                        a1, b1, c1 = k
                        Mk = cache[k] = _integer_moebius_matrix(a1, b1, c1, P, int(pN))
                    M += m * Mk
                M = matrix(ZZ, P, P, {rc : o % pN for rc, o in M.dict().items()})
                # The normalization (value 0 at t = 0) is linear: kill column 0
                M.set_column(0, [0] * P)
                track.append((j * P, i * P, M.dict(), moebius_prec[j, i]))
                # As row vectors: G_i = sum_j F_j * M_ji
                A.set_block(j * P, i * P, M)
        else:
            # The multiplication by x is the integer matrix sum_b x_b R[b]. Compute
            # all of them at once: rows of X are coordinates, and the rows of
            # Rflat the matrices R[b], flattened.
            Rflat = matrix(ZZ, [Rb.list() for Rb in O.R])
            mult = lambda y : _reduce_columns(sum((ZZ(c) * Rb for c, Rb in zip(O.coords(y), O.R)), matrix(ZZ, d, d)), mods)
            imods = [int(o) for o in mods]
            positions = []
            X = []
            for (j, i), lst in blocks.items():
                block_entries = {}
                for m, k, coeffs in lst:
                    try:
                        entries = cache[k]
                    except KeyError:
                        Ra, Rb, Rc = [mult(o) for o in coeffs]
                        # The coordinates of the entries of the action matrix
                        entries = cache[k] = _coordinate_moebius_entries(Ra, Rb, Rc, P, mods)
                    for r, c, u in entries:
                        if c == 0:
                            continue # The normalization (value 0 at t = 0) kills column 0
                        old = block_entries.get((r, c))
                        if old is None:
                            block_entries[r, c] = [(m * x) % md for x, md in zip(u, imods)]
                        else:
                            block_entries[r, c] = [(x + m * y) % md for x, y, md in zip(old, u, imods)]
                block_entries = {rc : u for rc, u in block_entries.items() if any(u)}
                for (r, c), u in block_entries.items():
                    # As row vectors: G_i = sum_j F_j * M_ji
                    positions.append(((j * P + r) * d, (i * P + c) * d))
                    X.append(u)
                track.append((j * P, i * P, block_entries, moebius_prec[j, i]))
            Y = (matrix(ZZ, len(X), d, X) * Rflat).list() if X else []
            entries_A = {}
            k = 0
            for row, col in positions:
                for b1 in range(d):
                    for b2 in range(d):
                        val = Y[k] % mods[b2]
                        k += 1
                        if val:
                            entries_A[row + b1, col + b2] = val
            A = entries_A
        exps = [ZZ(md).valuation(O.p) if md > 1 else 0 for md in mods] * (n * P)
        self._operator = _IntegerOperator(A, O.p, exps, d, mode=mode, size=(n * P * d, n * P * d))
        self._tracker = _PrecisionTracker(track, O, N, min(list(moebius_prec.values()) + [N]))
        # The smallest precision of the action matrices (at most P): if the
        # inputs are known modulo pi^P and this is P, so are the outputs, and
        # there is no need to track the precision.
        self.min_input_prec = self._tracker.min_input_prec
        # How to represent the vectors
        self._dense = (d == 1 and self._operator.mode == 'dense')
        if self._dense:
            # A single modulus: use Sage's integer vectors (FLINT)
            self._pN = mods[0]
        else:
            # Vectors are lists of python integers, coordinate k reduced modulo mods[k]
            self._mods = [int(o) for o in mods] * (n * P)

    def reduce(self, w):
        r'''
        Reduce the coordinates of w modulo pi^P.
        '''
        if self._dense:
            pN = self._pN
            return vector(ZZ, w).apply_map(lambda o : o % pN)
        return [o % md for o, md in zip(w, self._mods)]

    def apply(self, w):
        r'''
        The image of w (not reduced, see reduce).
        '''
        if self._dense:
            return w * self._operator.A
        return self._operator.apply(w)

    def add(self, a, b):
        if self._dense:
            return a + b
        return [x + y for x, y in zip(a, b)]

    def sub(self, a, b):
        if self._dense:
            return a - b
        return [x - y for x, y in zip(a, b)]

    def valuation(self, w):
        r'''
        The smallest valuation of the coefficients represented by w (at most P).
        '''
        return self.O.valuation(w, self.P)

    def to_vector(self, elts):
        r'''
        The vector of coordinates of the list elts of nP integral elements of
        K (the concatenation of the coefficients of n log-series).
        '''
        O = self.O
        return self.reduce([int(c) for o in elts for c in O.coords(o)])

    def initial_precisions(self, elts):
        r'''
        The absolute precisions (at most P) of the list of elements elts of
        K, to be used with propagate.
        '''
        import numpy as np
        N = self.P
        return np.array([int(min(o.precision_absolute(), N)) for o in elts], dtype=np.int64)

    def propagate(self, precs, w):
        r'''
        The precisions of the coefficients of the image of w, given those of
        the coefficients of w. As for p-adic elements, the error of a sum of
        products F_j[r] * M[r, c] has valuation at least
        min(prec(F_j[r]) + val(M[r, c]), prec(M[r, c]) + val(F_j[r])).
        '''
        import numpy as np
        O, N = self.O, self.P
        src, dst, Mval, Mprec, targets, starts = self._tracker.arrays
        vals = np.array(O.element_valuations(w, N), dtype=np.int64)
        ans = np.full(len(precs), int(N), dtype=np.int64)
        if len(src):
            # The entries are sorted by target
            q = np.minimum(precs[src] + Mval, Mprec + vals[src])
            ans[targets] = np.minimum(ans[targets], np.minimum.reduceat(q, starts))
        return ans

    def to_values(self, w, precs):
        r'''
        The list of the n vectors over K of coefficients of the log-series
        represented by w, with the given precisions.
        '''
        K, O, P = self.K, self.O, self.P
        d = O.d
        return [vector(K, [O.element(w[(b * P + r) * d : (b * P + r + 1) * d], int(precs[b * P + r]))
                           for r in range(P)])
                for b in range(self.n)]


def _log_series_length(prec, p, e):
    r'''
    The number of coefficients of log F that are needed for the remaining
    ones to vanish modulo pi^prec, where F is a product of factors (1 - x t)
    with x in the maximal ideal. The k-th coefficient of log(1 - x t) has
    valuation at least k - e * v_p(k) >= k - e * log_p(k), which is
    increasing in k for k >= e / ln(p).
    '''
    lnp = float(_log(p))
    length = prec
    while length * lnp < e or length - e * float(_log(length)) / lnp < prec:
        length += 1
    return length


class AdditiveMeromorphicFunctionsElement(ModuleElement):
    r'''
    A meromorphic function F that is a principal unit (see
    AdditiveMeromorphicFunctions), stored as the vector of coefficients of
    log F(t), where t is the coordinate given by the parameter, normalized
    by log F(0) = 0. It has parent.series_length() coefficients, known
    modulo pi^prec.
    '''
    def __init__(self, parent, data, parameter=None, check=True):
        ModuleElement.__init__(self, parent)
        if parameter is None:
            parameter = parent._identity
        if check:
            K = parent.base_ring()
            prec = parent._prec
            length = parent._length
            if parameter is not parent._identity:
                parameter = set_immutable(Matrix(K, 2, 2, parameter))
            if isinstance(data, AdditiveMeromorphicFunctionsElement):
                value, parameter = data._value, data._parameter
            elif isinstance(data, LogSeries):
                value, parameter = data._value, data._parameter
            elif isinstance(data, MeromorphicFunctionsElement):
                # Only the coefficients up to the precision of data are known
                value, parameter = data.power_series().log().list(), data._parameter
            elif isinstance(data, DivisorsElement):
                value = log_series_of_divisor(data, parameter, length)
            elif isinstance(data, (int, Integer)):
                if data != 0:
                    raise ValueError('Only the constant function 1 (that is, 0) is allowed')
                value = []
            else:
                value = data
            value = [K(o) for o in list(value)[:length]]
            value += [K(0)] * (length - len(value))
            value[0] = K(0)
            self._value = vector(K, [o.add_bigoh(prec) for o in value])
        else:
            self._value = data
        self._parameter = parameter

    @lazy_attribute
    def _log_series(self):
        return LogSeries(self._value, self._parameter)

    def power_series(self):
        r'''
        The power series log F(t).
        '''
        return self.parent().power_series_ring()(list(self._value))

    def to_multiplicative(self):
        r'''
        The same function, as an element of MeromorphicFunctions (with the
        same precision).
        '''
        parent = self.parent()
        prec = parent._prec
        M = MeromorphicFunctions(parent.base_ring(), parent.prime(), prec)
        return M(self.power_series().add_bigoh(prec).exp().list(), self._parameter)

    def __call__(self, D):
        return self.evaluate(D)

    def evaluate(self, D, prec=None):
        r'''
        The logarithm of the value of F at the point or degree-zero divisor D.
        '''
        if isinstance(D, (int, Integer)):
            D = self.parent().base_ring()(D)
        ans = self._log_series.evaluate(D, prec)
        if isinstance(ans, int): # empty divisor
            ans = self.parent().base_ring()(ans)
        return ans

    def evaluate_multiplicative(self, D, prec=None):
        r'''
        The value of F at the point or degree-zero divisor D.
        '''
        return exp_small(self.evaluate(D, prec))

    def pair_with(self, D, multiplicative=False):
        if multiplicative:
            return self.evaluate_multiplicative(D)
        else:
            return self.evaluate(D)

    def eval_dlog(self, D):
        r'''
        The logarithmic derivative of F at the point D.
        '''
        if isinstance(D, (int, Integer)):
            D = self.parent().base_ring()(D)
        if isinstance(D, DivisorsElement):
            raise NotImplementedError
        return self._log_series.eval_dlog(D)

    def eval_derivative(self, D, return_value=False):
        val = self.evaluate_multiplicative(D)
        ans = val * self.eval_dlog(D)
        if return_value:
            return ans, val
        else:
            return ans

    def _richcmp_(self, right, op):
        return richcmp(list(self._value), list(right._value), op)

    def __bool__(self):
        return any(not o.is_zero() for o in self._value)

    __nonzero__ = __bool__

    def valuation(self, p=None):
        return min([o.valuation(p) for o in self._value[1:]], default=Infinity)

    def _add_(self, right):
        if self._parameter is not right._parameter and self._parameter != right._parameter:
            raise RuntimeError("Trying to add incompatible series")
        return self.__class__(self.parent(), self._value + right._value, self._parameter, check=False)

    def _sub_(self, right):
        if self._parameter is not right._parameter and self._parameter != right._parameter:
            raise RuntimeError("Trying to subtract incompatible series")
        return self.__class__(self.parent(), self._value - right._value, self._parameter, check=False)

    def _neg_(self):
        return self.__class__(self.parent(), -self._value, self._parameter, check=False)

    def scale_by(self, k):
        return self.__class__(self.parent(), k * self._value, self._parameter, check=False)

    def _repr_(self):
        return 'exp(%s)' % self.power_series()

    def _acted_upon_(self, g, on_left):
        if isinstance(g, (int, Integer)):
            return self.scale_by(g)
        else:
            return self.left_act_by_matrix(g)

    def fast_act(self, key):
        M, param = key
        ans = self._value * M
        ans[0] = 0
        return self.__class__(self.parent(), ans, param, check=False)

    def left_act_by_matrix(self, g, param=None):
        r'''
        Same as MeromorphicFunctionsElement.left_act_by_matrix: compose with
        the Mobius transformation, and normalize so that the value at 0 is 0
        (the multiplicative version divides by the value at 0 instead).
        '''
        if param is None:
            param = self._parameter
        M = self.parent().get_action_data(g, self._parameter, param)
        ans = self._value * M
        ans[0] = 0
        return self.__class__(self.parent(), ans, param, check=False)


class AdditiveMeromorphicFunctions(Parent, UniqueRepresentation):
    r'''
    Additive version of MeromorphicFunctions.

    MeromorphicFunctions represents a function F on the closed unit disk (in
    the coordinate t given by a parameter) by its power series, normalized by
    F(0) = 1, and the group law (the product of functions) by the product of
    power series. When F is a principal unit, that is, all the coefficients of
    F - 1 lie in the maximal ideal (as for the functions of divisors supported
    outside the disk, see log_series_of_divisor), we can store log F instead,
    so that products become sums. Composing with the action of matrices (the
    matrices of get_action_data) commutes with taking logarithms, and the
    normalization F(0) = 1 becomes log F(0) = 0.

    The values of F at the points of the disk are principal units, which are
    recovered from those of log F with the exponential. This needs exp and log
    to be inverse isomorphisms between the principal units and the maximal
    ideal, that is e < p - 1.

    The k-th coefficient of log(1 - x t) is x^k / k, whose valuation can be
    smaller than that of the k-th coefficient x^k of 1 - x t. So, in order to
    get the precision prec of MeromorphicFunctions(K, p, prec), the series
    log F have a few more coefficients (see series_length).

    Linear combinations of the actions of matrices are much faster with
    integer matrices, see LogSeriesOperator.

    EXAMPLES::

        sage: from darmonpoints.meromorphic import MeromorphicFunctions, AdditiveMeromorphicFunctions
        sage: from darmonpoints.divisors import Divisors
        sage: K.<a> = Qq(25, 20)
        sage: M = MeromorphicFunctions(K, 5, 20)
        sage: A = AdditiveMeromorphicFunctions(K, 5, 20)
        sage: Div = Divisors(K)
        sage: D = Div([(1, a/5), (-1, (a + 1)/5), (2, 1/(25*a)), (-2, 3/25)])
        sage: E = Div([(1, a + 2), (-1, K(3))])
        sage: f = A(D)

    The values are those of the multiplicative implementation::

        sage: f.evaluate_multiplicative(E) == M(D).evaluate(E)
        True
        sage: f.evaluate(E) == M(D).evaluate(E).log()
        True
        sage: f.to_multiplicative().evaluate(E) == M(D).evaluate(E)
        True

    Sums correspond to products, and the actions of matrices agree::

        sage: D2 = Div([(1, 2/5), (-1, a/25)])
        sage: (f - 3 * A(D2)).evaluate_multiplicative(E) == M(D).evaluate(E) / M(D2).evaluate(E)^3
        True
        sage: g = matrix(K, 2, 2, [1, a, 5, 3])
        sage: (g * f).evaluate_multiplicative(E) == (g * M(D)).evaluate(E)
        True
        sage: A(g * D) == g * f
        True

    It needs e < p - 1::

        sage: AdditiveMeromorphicFunctions(Qp(2, 10), 2, 10)
        Traceback (most recent call last):
        ...
        NotImplementedError: The additive implementation needs e < p - 1
    '''
    Element = AdditiveMeromorphicFunctionsElement

    @staticmethod
    def __classcall__(cls, K, p, prec, **kwargs):
        return super().__classcall__(cls, K, p, prec)

    def __init__(self, K, p, prec):
        Parent.__init__(self)
        q, e = _ramification_data(K)
        if e >= q - 1:
            raise NotImplementedError('The additive implementation needs e < p - 1')
        if prec is None:
            prec = K.precision_cap()
        self._p = p
        self._prec = prec
        self._length = _log_series_length(prec, q, e)
        self._base_ring = K
        # Used for the action data and the power series ring
        self._multiplicative = MeromorphicFunctions(K, p, self._length)
        self._identity = set_immutable(Matrix(K, 2, 2, 1))

    def prime(self):
        return self._p

    def series_length(self):
        r'''
        The number of coefficients of the series log F (see
        _log_series_length).

        EXAMPLES::

            sage: from darmonpoints.meromorphic import AdditiveMeromorphicFunctions
            sage: AdditiveMeromorphicFunctions(Qq(25, 60, names='a'), 5, 60).series_length()
            63
        '''
        return self._length

    def base_ring(self):
        return self._base_ring

    def power_series_ring(self):
        return self._multiplicative.power_series_ring()

    def get_action_data(self, g, oldparam, param, prec=None):
        r'''
        Same as MeromorphicFunctions.get_action_data (the action on
        log-series is given by the same matrices).
        '''
        return self._multiplicative.get_action_data(g, oldparam, param, prec)

    def compute_action_data(self, g, oldparam, param, prec=None):
        return self._multiplicative.compute_action_data(g, oldparam, param, prec)

    def _element_constructor_(self, data, param=None, check=True):
        return self.element_class(self, data, parameter=param, check=check)

    def _repr_(self):
        return (
            "Meromorphic Additive Functions over %s with p = %s and prec = %s"
            % (self._base_ring, self._p, self._prec)
        )
