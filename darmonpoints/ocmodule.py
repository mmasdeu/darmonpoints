#########################################################################
#       Copyright (C) 2011 Cameron Franc and Marc Masdeu
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#                  http://www.gnu.org/licenses/
#########################################################################
import operator

from sage.categories.action import Action
from sage.categories.pushout import pushout
from sage.matrix.constructor import Matrix
from sage.matrix.matrix_space import MatrixSpace
from sage.misc.all import cputime
from sage.misc.cachefunc import cached_method
from sage.misc.misc_c import prod
from sage.misc.verbose import get_verbose, set_verbose, verbose
from sage.modular.pollack_stevens.sigma0 import Sigma0, Sigma0ActionAdjuster
from sage.modules.free_module_element import FreeModuleElement_generic_dense
from sage.modules.module import Module
from sage.modules.vector_integer_dense import Vector_integer_dense
from sage.rings.all import Integer, Zp
from sage.rings.finite_rings.integer_mod_ring import Zmod
from sage.rings.infinity import Infinity
from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import Qp, ZpCA
from sage.rings.padics.padic_generic import pAdicGeneric
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

from .homology import Divisors
from .rationalfunctions import RationalFunctions
from .representations import MatrixAction, Scaling


class our_adjuster(Sigma0ActionAdjuster):
    """
    Callable object that turns matrices into 4-tuples.

    EXAMPLES::

        sage: from sage.modular.btquotients.pautomorphicform import _btquot_adjuster
        sage: adj = _btquot_adjuster()
        sage: adj(matrix(ZZ,2,2,[1..4]))
        (4, 2, 3, 1)
    """

    def __call__(self, g):
        a, b, c, d = g.list()
        return tuple([d, b, c, a])


class ps_adjuster(Sigma0ActionAdjuster):
    """
    Callable object that turns matrices into 4-tuples.

    """

    def __call__(self, g):
        a, b, c, d = g.list()
        return tuple([a, -b, -c, d])


class OCVnElement(ModuleElement):
    r"""
    This class represents elements in an overconvergent coefficient module.

    INPUT:

     - ``parent`` - An overconvergent coefficient module.

     - ``val`` - The value that it needs to store (default: 0). It can be another OCVnElement,
       in which case the values are copied. It can also be a column vector (or something
       coercible to a column vector) which represents the values of the element applied to
       the polynomials `1`, `x`, `x^2`, ... ,`x^n`.

     - ``check`` - boolean (default: True). If set to False, no checks are done and ``val`` is
       assumed to be the a column vector.

    AUTHORS:

    - Cameron Franc (2012-02-20)
    - Marc Masdeu (2012-02-20)
    """

    def __init__(self, parent, val=0, check=True, normalize=False):
        ModuleElement.__init__(self, parent)
        self._parent = parent
        self._depth = self._parent._depth
        if not check:
            self._val = val
        else:
            if isinstance(val, self.__class__):
                if val._parent._depth == parent._depth:
                    self._val = val._val
                else:
                    d = min([val._parent._depth, parent._depth])
                    self._val = val._val.submatrix(0, 0, nrows=d)

            elif isinstance(val, Vector_integer_dense) or isinstance(
                val, FreeModuleElement_generic_dense
            ):
                self._val = MatrixSpace(self._parent._R, self._depth, 1)(0)
                for i, o in enumerate(val.list()):
                    self._val[i, 0] = o
            elif hasattr(val, "parent") and isinstance(
                val.parent(), AddMeromorphicFunctions
            ):
                p = self._parent._Rmod.prime()
                if val.parent().twisting_matrix() != Matrix(
                    ZZ, 2, 2, [0, 1, p, 0]
                ) and val.parent().twisting_matrix() != Matrix(ZZ, 2, 2, [0, 1, 1, 0]):
                    raise NotImplementedError
                self._val = MatrixSpace(self._parent._R, self._depth, 1)(0)
                c = val.parent().twisting_matrix()[1, 0]
                for i in range(1, self._depth):
                    if val._value[i - 1, 1] != 0:
                        raise NotImplementedError(
                            "Meromorphic function seems to be using values in quadratic extension"
                        )
                    self._val[i, 0] = -val._value[i - 1, 0].lift() // c**i
            else:
                try:
                    self._val = Matrix(self._parent._R, self._depth, 1, val)
                except (TypeError, ValueError):
                    self._val = self._parent._R(val) * MatrixSpace(
                        self._parent._R, self._depth, 1
                    )(1)
        self._moments = self._val

    def lift(self, p=None, M=None):
        return self

    def moment(self, i):
        return self._parent._Rmod(self._moments[i, 0])

    def moments(self):
        return self._moments.list()

    def __getitem__(self, r):
        r"""
        Returns the value of ``self`` on the polynomial `x^r`.

        INPUT:
          - ``r`` - an integer. The power of `x`.

        EXAMPLES:

        """
        return self._val[r, 0]

    def __setitem__(self, r, val):
        r"""
        Sets the value of ``self`` on the polynomial `x^r` to ``val``.

        INPUT:
        - ``r`` - an integer. The power of `x`.
        - ``val`` - a value.

        EXAMPLES:

        """
        self._val[r, 0] = val

    def element(self):
        r"""
        The element ``self`` represents.
        """
        tmp = self.matrix_rep()
        return [tmp[ii, 0] for ii in range(tmp.nrows())]

    def list(self):
        r"""
        The element ``self`` represents.
        """
        return self.element()

    def matrix_rep(self):
        r"""
        Returns a matrix representation of ``self``.
        """
        B = self._parent.basis()
        A = Matrix(
            self._parent._R,
            self._parent.dimension(),
            self._parent.dimension(),
            [[b._val[ii, 0] for b in B] for ii in range(self._depth)],
        )
        if A == 1:
            return MatrixSpace(self._parent._R, self._parent.dimension(), 1)(self._val)
        else:
            return A.solve_right(self._val)

    def _add_(self, y):
        r"""
        Add two elements.
        """
        val = self._val + y._val
        return self.__class__(self._parent, val, check=False)

    def _sub_(self, y):
        r"""
        Subtract two elements.
        """
        val = self._val - y._val
        return self.__class__(self._parent, val, check=False)

    def _div_(self, right):
        r"""
        Finds the scalar such that self = a * right (assuming that it exists)
        """
        if self.is_zero():
            return 0
        else:
            a = None
            for u, v in zip(self._moments, right._moments):
                if u != 0:
                    a = u / v
                    break
            assert a is not None
            assert (self - a * right).is_zero(), "Not a scalar multiple of right"
            return a

    def r_act_by(self, x):
        r"""
        Act on the right by a matrix.
        """
        return self._acted_upon_(x.adjugate(), False)

    def _acted_upon_(self, x, right_action):  # Act by x on the left
        try:
            x = x.matrix()
        except AttributeError:
            pass
        if right_action:
            return self._acted_upon_(x.adjugate(), False)
        else:
            tmp = self._parent._get_powers(x) * self._val
            return self.__class__(self._parent, tmp, check=False)

    def _neg_(self):
        return self.__class__(self._parent, -self._val, check=False)

    def _rmul_(self, a):
        # assume that a is a scalar
        return self.__class__(
            self._parent, self._parent._Rmod(a) * self._val, check=False
        )

    def _repr_(self):
        r"""
        Returns the representation of self as a string.
        """
        R = PowerSeriesRing(self._parent._R, default_prec=self._depth, name="z")
        z = R.gen()
        return str(sum([R(self._val[ii, 0] * z**ii) for ii in range(self._depth)]))

    def _cmp_(self, other):
        return (self._val > other._val) - (self._val < other._val)

    def __nonzero__(self):
        return self._val != 0

    def evaluate_at_poly(self, P, R=None, depth=None):
        r"""
        Evaluate ``self`` at a polynomial
        """
        p = self._parent._p
        if R is None:
            try:
                R = pushout(P.parent().base_ring(), self.parent().base_ring())
            except AttributeError:
                R = self.parent().base_ring()
        if depth is None and hasattr(P, "degree"):
            try:
                depth = min([P.degree() + 1, self._depth])
                return sum(R(self._val[ii, 0]) * P[ii] for ii in range(depth))
            except NotImplementedError:
                pass
            return R(self._val[0, 0]) * P
        else:
            return sum(R(self._val[ii, 0]) * P[ii] for ii in range(self._depth))

    def valuation(self, l=None):
        r"""
        The `l`-adic valuation of ``self``.

        INPUT: a prime `l`. The default (None) uses the prime of the parent.

        """
        if not self._parent.base_ring().is_exact():
            if not l is None and l != self._parent._Rmod.prime():
                raise ValueError("This function can only be called with the base prime")
            l = self._parent._Rmod.prime()
            return min([self._val[ii, 0].valuation(l) for ii in range(self._depth)])
        else:
            return min([self._val[ii, 0].valuation(l) for ii in range(self._depth)])

    def valuation_list(self, l=None):
        r"""
        The `l`-adic valuation of ``self``, as a list.

        INPUT: a prime `l`. The default (None) uses the prime of the parent.

        """
        if not self._parent.base_ring().is_exact():
            if not l is None and l != self._parent._Rmod.prime():
                raise ValueError("This function can only be called with the base prime")
            l = self._parent._Rmod.prime()
            return [self._val[ii, 0].valuation(l) for ii in range(self._depth)]
        else:
            return [self._val[ii, 0].valuation(l) for ii in range(self._depth)]

    def reduce_mod(self, N=None):
        if N is None:
            N = self.parent()._pN
        self._val = self._val.apply_map(lambda x: x % N)
        return self


class OCVn(Module, UniqueRepresentation):
    Element = OCVnElement
    r"""
    This class represents objects in the overconvergent approximation modules used to
    describe overconvergent p-adic automorphic forms.

    INPUT:

     - ``n`` - integer

     - ``R`` - ring

     - ``depth`` - integer (Default: None)

     - ``basis`` - (Default: None)


    AUTHORS:

    - Cameron Franc (2012-02-20)
    - Marc Masdeu (2012-02-20)

    """

    def __init__(self, p, depth):
        Module.__init__(self, base=Zmod(p ** (depth - 1)))
        self._R = Zmod(p ** (depth - 1))
        self._p = p
        self._Rmod = ZpCA(p, depth - 1)
        self._depth = depth
        self._pN = self._p ** (depth - 1)
        self._PowerSeries = PowerSeriesRing(
            self._Rmod, default_prec=self._depth, name="z"
        )
        self._cache_powers = dict()
        self._unset_coercions_used()
        self._Sigma0 = Sigma0(self._p, base_ring=self._Rmod, adjuster=our_adjuster())
        self.register_action(Sigma0Action(self._Sigma0, self))
        self._populate_coercion_lists_()

    def Sigma0(self):
        return self._Sigma0

    def approx_module(self, M=None):
        if M is None:
            M = self._depth
        return MatrixSpace(self._R, M, 1)

    def clear_cache(self):
        del self._cache_powers
        self._cache_powers = dict()

    def is_overconvergent(self):
        return True

    def _an_element_(self):
        r""" """
        return OCVnElement(
            self,
            Matrix(self._R, self._depth, 1, range(1, self._depth + 1)),
            check=False,
        )

    def _coerce_map_from_(self, S):
        # Nothing coherces here, except OCVnElement
        return False

    def _element_constructor_(self, x, check=True, normalize=False):
        # Code how to coherce x into the space
        # Admissible values of x?
        return OCVnElement(self, x)

    def acting_matrix(self, g, M):
        try:
            g = g.matrix()
        except AttributeError:
            pass
        return self._get_powers(g).submatrix(0, 0, M, M)

    def _get_powers(self, abcd, emb=None):
        abcd = tuple(abcd.list())
        try:
            return self._cache_powers[abcd]
        except KeyError:
            pass
        R = self._PowerSeries
        if emb is None:
            a, b, c, d = abcd
        else:
            a, b, c, d = emb(abcd).list()
        r = R([b, a])
        s = R([d, c])
        ratio = r * s**-1
        y = R.one()
        xlist = [[1] + [0 for o in range(self._depth - 1)]]
        for ii in range(1, self._depth):
            y *= ratio
            ylist = y.list()[: self._depth]
            ylist.extend(
                [R.base_ring().zero() for o in range(self._depth - len(ylist))]
            )
            xlist.append([ZZ(o) for o in ylist])
        x = Matrix(ZZ, self._depth, self._depth, xlist)
        self._cache_powers[abcd] = x
        return x

    def _repr_(self):
        r"""
        This returns the representation of self as a string.
        """
        return "Space of %s-adic distributions with k=0 action and precision cap %s" % (
            self._p,
            self._depth - 1,
        )

    def prime(self):
        return self._p

    def basis(self):
        r"""
        A basis of the module.

        INPUT:

         - ``x`` - integer (default: 1) the description of the
           argument x goes here.  If it contains multiple lines, all
           the lines after the first need to be indented.

         - ``y`` - integer (default: 2) the ...

        """
        try:
            return self._basis
        except:
            pass
        self._basis = [
            OCVnElement(
                self,
                Matrix(self._R, self._depth, 1, {(jj, 0): 1}, sparse=False),
                check=False,
            )
            for jj in range(self._depth)
        ]
        return self._basis

    def base_ring(self):
        r"""
        This function returns the base ring of the overconvergent element.
        """
        return self._Rmod

    def depth(self):
        r"""
        Returns the depth of the module.
        """
        return self._depth

    def dimension(self):
        r"""
        Returns the dimension (rank) of the module.
        """
        return self._depth

    def precision_cap(self):
        r"""
        Returns the dimension (rank) of the module.
        """
        return self._depth

    def is_exact(self):
        return False


class Sigma0Action(Action):
    def __init__(self, G, M):
        Action.__init__(self, G, M, is_left=True, op=operator.mul)

    def _act_(self, g, v):
        return v._acted_upon_(g.matrix(), False)


class AddMeromorphicFunctionsElement(ModuleElement):
    def __init__(self, parent, data, check=True):
        ModuleElement.__init__(self, parent)
        if check:
            K = parent.base_ring()
            prec = parent._prec
            p = K.prime()
            Ps = parent._Ps
            phi = parent._divisor_to_pseries
            if data == 0:
                self._value = parent._V(0)
            elif isinstance(data.parent(), OCVn):
                if parent.twisting_matrix() != Matrix(
                    ZZ, 2, 2, [0, 1, p, 0]
                ) and parent.twisting_matrix() != Matrix(ZZ, 2, 2, [0, 1, 1, 0]):
                    raise NotImplementedError
                self._value = Matrix(Zmod(K.prime() ** prec), prec, 2)
                c = parent.twisting_matrix()[1, 0]
                for i in range(prec):
                    self._value[i, 0] = -data.moment(i + 1) * c ** (
                        i + 1
                    )  # DEBUG the p-power
            elif isinstance(data.parent(), Divisors):
                self._value = parent._V(0)
                for Q, n in data:
                    self._value += n * parent._V(
                        [
                            o._polynomial_list(pad=True)
                            for o in (phi(K(Q)).log().derivative()).list()
                        ]
                    )
            elif isinstance(data.parent(), RationalFunctions):
                rf = data.rational_function()
                t = rf.parent().gen()
                a, b, c, d = parent.twisting_matrix().list()
                rf = Ps(rf((a * t + b) / (c * t + d)))
                rf /= rf(K(0))
                ans = parent._V(0)
                rflogp = rf.log().derivative()
                for a, i in zip(rflogp.coefficients(), rflogp.exponents()):
                    try:
                        ans.set_row(i, a._polynomial_list(pad=True))
                    except ValueError:
                        pass
                self._value = ans
            elif data.parent() == parent._V:
                self._value = parent._V(data)
            elif hasattr(data, "nrows"):  # A matrix
                self._value = parent._V(data)
            else:
                val = Ps(data)
                val.add_bigoh(prec)
                self._value = parent._V(
                    [o._polynomial_list(pad=True) for o in val.list()]
                )
        else:
            self._value = data
        self._moments = self._value

    def power_series(self):
        K = self.parent().base_ring()
        Ps = self.parent().power_series_ring()
        return Ps([K(o.list()) for o in self._value.rows()])

    def __call__(self, D):
        ans = self.evaluate_additive(D)
        if ans == 0:
            return ans.parent().one()
        else:
            return ans.exp()

    def pair_with(self, D):
        return self.evaluate_additive(D)

    def evaluate_multiplicative(self, D):
        K = self.parent().base_ring()
        p = K.prime()
        assert isinstance(D.parent(), Divisors) and D.degree() == 0
        phi = self.parent()._eval_pseries_map
        poly = self.power_series().integral().exp().polynomial()
        ans = K(1)
        for P, n in D:
            phiP = phi(P)
            if phiP.valuation() < 0:
                raise ValueError("Negative valuation!")
            ans *= poly(phiP) ** n
        return ans  # K(1) if ans == 0 else ans.exp()

    def evaluate_additive(self, D):
        K = self.parent().base_ring()
        p = K.prime()
        assert isinstance(D.parent(), Divisors) and D.degree() == 0
        phi = self.parent()._eval_pseries_map
        poly = self.power_series().polynomial()
        poly = poly.integral()
        ans = K(0)
        for P, n in D:
            phiP = phi(P)
            if phiP.valuation() < 0:
                raise ValueError("Negative valuation!")
            ans += n * poly(phiP)
        if ans == 0:
            return K(0)
        else:
            return ans

    def _cmp_(self, right):
        return (self._value > right._value) - (self._value < right._value)

    def __nonzero__(self):
        return self._value != 0

    def valuation(self, p=None):
        K = self.parent().base_ring()
        return min([Infinity] + [K(o.list()).valuation(p) for o in self._value.rows()])

    def _add_(self, right):
        ans = self._value + right._value
        return self.__class__(self.parent(), ans, check=False)

    def _sub_(self, right):
        ans = self._value - right._value
        return self.__class__(self.parent(), ans, check=False)

    def _neg_(self):
        ans = -self._value
        return self.__class__(self.parent(), ans, check=False)

    def _repr_(self):
        return repr(self._value)

    def scale_by(self, k):
        ans = k * self._value
        return self.__class__(self.parent(), ans, check=False)

    def left_act_by_matrix(self, g):  # meromorphic functions
        Ps = self._value.parent()
        K = Ps.base_ring()
        # Below we code the action which is compatible with the usual action
        # P |-> (aP+b)/(cP+D)
        M = self.parent().get_action_data(g)
        ans = M * self._value
        return self.__class__(self.parent(), ans, check=False)


class AddMeromorphicFunctions(Parent, CachedRepresentation):
    r"""
    TESTS:

    sage: from darmonpoints.ocmodule import AddMeromorphicFunctions
    sage: from darmonpoints.homology import Divisors
    sage: from darmonpoints.sarithgroup import BigArithGroup
    sage: padic_printing.mode('val-unit')
    sage: K.<a> = Qq(7^2,5)
    sage: G = BigArithGroup(7,1,1,use_shapiro=False, outfile='/dev/null')
    sage: M = AddMeromorphicFunctions(K)
    sage: Div = Divisors(K)
    sage: D = Div(a/7) - Div((a+1)/7)
    sage: f = M(D)
    sage: f.power_series()
    7 * (1205 + 401*a) + O(7^5) + (7^2 * (59 + 229*a) + O(7^5))*t + (7^3 * (23 + 13*a) + O(7^5))*t^2 + (7^4 * (6 + 2*a) + O(7^5))*t^3 + O(7^5)*t^4
    sage: E = Div((a+3)) - Div((a+2))
    sage: f(E).log(0) == D.pair_with(E)
    True
    sage: g = G.Gpn.gen(1).quaternion_rep
    sage: M(g * D)(E) == (g * f)(E)
    True
    sage: M = AddMeromorphicFunctions(K, twisting_matrix = G.wp())
    sage: Div = Divisors(K)
    sage: D = Div(a) - Div((a+1))
    sage: f = M(D)
    sage: f.power_series()
    7 * 2400 + O(7^5) + (7^2 * (1 + 2*a) + O(7^5))*t + (7^3 * (8 + 15*a) + O(7^5))*t^2 + (7^4 * (6 + 2*a) + O(7^5))*t^3 + O(7^5)*t^4
    sage: E = Div((a+3)/7) - Div((a+2)/7)
    sage: f(E).log(0) == D.pair_with(E)
    True
    sage: g = G.Gpn.gen(1).quaternion_rep
    sage: A = M(g * D)(E)
    sage: B = (g * f)(E)
    sage: A == B
    True
    """
    Element = AddMeromorphicFunctionsElement

    def __init__(self, K, twisting_matrix=None):
        Parent.__init__(self)
        self._base_ring = K
        self._prec = K.precision_cap()
        psprec = self._prec + 1
        self._Ps = PowerSeriesRing(self._base_ring, names="t", default_prec=psprec)
        self._V = MatrixSpace(Zmod(K.prime() ** self._prec), self._prec, 2)
        t = self._Ps.gen()
        if twisting_matrix is None:
            self._twisting_matrix = Matrix(QQ, 2, 2, 1)
        else:
            self._twisting_matrix = twisting_matrix
        a, b, c, d = self._twisting_matrix.list()
        # Maps Q to 1 - t / ((a*Q+b)/(c*Q+d))
        self._divisor_to_pseries = lambda Q: 1 - (
            Q.parent()(c) * Q + Q.parent()(d)
        ) * t / (Q.parent()(a) * Q + Q.parent()(b))
        a, b, c, d = (self._twisting_matrix**-1).list()
        self._eval_pseries_map = lambda Q: (Q.parent()(a) * Q + Q.parent()(b)) / (
            Q.parent()(c) * Q + Q.parent()(d)
        )
        self._unset_coercions_used()
        self.register_action(Scaling(ZZ, self))
        self.register_action(MatrixAction(MatrixSpace(K, 2, 2), self))

    def acting_matrix(self, g, dim=None):
        try:
            g = g.matrix()
        except AttributeError:
            pass
        return self.get_action_data(g)

    def get_action_data(self, g, K=None):
        verb_level = get_verbose()
        set_verbose(0)
        prec = self._prec
        p = self.base_ring().prime()
        w = self.twisting_matrix()
        a, b, c, d = (w**-1 * g * w).list()
        if K is None:
            Zm = Zmod(p**prec)
            if hasattr(a, "lift"):
                a_inv = Zm((a**-1).lift())
                a, b, c, d = Zm(a.lift()), Zm(b.lift()), Zm(c.lift()), Zm(d.lift())
                K = Zmod(p**prec)
            else:
                a_inv = a**-1
                try:
                    a = Zm(a)
                    b = Zm(b)
                    c = Zm(c)
                    d = Zm(d)
                    a_inv = Zm(a_inv)
                except (TypeError, ValueError):
                    pass
                K = g.parent().base_ring()
        else:
            Zm = K
            a_inv = a**-1

        Ps = PowerSeriesRing(Zm, names="z", default_prec=prec)
        z = Ps.gen()
        denom = (
            (a_inv * (-c * a_inv * z + 1) ** -1).polynomial().truncate(prec)
        )  # 1 / (-c*z + a)
        zz = (d * z - b) * denom  # zz = (d * z - b) / (-c * z  + a)

        zz_ps0 = zz.truncate(prec)  # Ps(zz).add_bigoh(prec)
        zz_ps = (a * d - b * c) * (denom**2).truncate(
            prec
        )  # (a*d - b*c) * denom**2 # zz_ps = det(g) * (-c * z + a)**-2
        M = Matrix(ZZ, prec, prec, 0)
        for j in range(prec):
            for i, aij in enumerate(zz_ps.list()):
                M[i, j] = aij
            if j < prec - 1:  # Don't need the last multiplication
                zz_ps = (zz_ps0 * zz_ps).truncate(prec)
            else:
                set_verbose(verb_level)
                return M  # Contains, in each column j, the action of g on z^j: det(g) (-cz+a)**-2 * ((dz-b)/(-cz+a))**j

    def is_additive(self):
        return True

    def base_ring(self):
        return self._base_ring

    def power_series_ring(self):
        return self._Ps

    def _element_constructor_(self, data):
        return self.element_class(self, data)

    def _repr_(self):
        return "Meromorphic (Additive) Functions over %s" % (self._base_ring)

    def twisting_matrix(self):
        return self._twisting_matrix
