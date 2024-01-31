#########################################################################
#       Copyright (C) 2011 Cameron Franc and Marc Masdeu
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#                  http://www.gnu.org/licenses/
#########################################################################

import operator

from sage.categories.action import Action
from sage.categories.monoids import Monoids
from sage.categories.pushout import pushout
from sage.matrix.constructor import Matrix
from sage.matrix.matrix_space import MatrixSpace
from sage.misc.verbose import get_verbose, set_verbose, verbose
from sage.modular.pollack_stevens.sigma0 import (
    Sigma0,
    Sigma0ActionAdjuster,
    _default_adjuster,
)
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
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.rational_field import QQ
from sage.structure.element import Element, ModuleElement, MonoidElement
from sage.structure.factory import UniqueFactory
from sage.structure.parent import Parent
from sage.structure.richcmp import richcmp
from sage.structure.sage_object import load, save
from sage.structure.unique_representation import UniqueRepresentation

##===========================================================================================


class left_ps_adjuster(Sigma0ActionAdjuster):
    """
    Callable object that turns matrices into 4-tuples.

    EXAMPLES::

        sage: from darmonpoints.ocbianchi import left_ps_adjuster
        sage: adj = left_ps_adjuster()
        sage: adj(matrix(ZZ,2,2,[1..4]))
        (4, -2, -3, 1)

    """

    def __call__(self, g):
        a, b, c, d = g.list()
        return tuple([d, -b, -c, a])


##===========================================================================================
##
##                SIGMA_0(p) ACTION
##
##===========================================================================================


class Sigma0Squared(Parent, UniqueRepresentation):
    r"""
    Parent class representing the monoid Sigma_0(p) x Sigma_0(p).
    """

    def __init__(self, p, base_ring=None, adjuster=None):
        ## This is a parent in the category of monoids; initialise children
        Parent.__init__(self, category=Monoids())
        self.Element = Sigma0SquaredElement

        ## base data initialisation
        self._R = ZZ
        self._p = p
        if base_ring is None:
            base_ring = ZpCA(p, 20)  ## create Zp
        self._Rmod = base_ring

        ## underlying Sigma_0(p)
        self._Sigma0 = Sigma0(self._p, base_ring=base_ring, adjuster=adjuster)
        self._populate_coercion_lists_()

    def _an_element_(self):
        return Sigma0SquaredElement(
            self, (self._Sigma0([1, 0, 0, 1]), self._Sigma0([1, 0, 0, -1]))
        )

    def _element_constructor_(self, first, second):
        r"""
        Element constructor. Takes as input tuple (g,h) of elments
        of Sigma_0(p) and represents the element (g,h) in the product.
        """
        return Sigma0SquaredElement(self, (self._Sigma0(first), self._Sigma0(second)))

    def level(self):
        """
        Returns the underlying level.
        """
        return self._p

    def base_ring(self):
        """
        Returns the underlying base ring (Zp).
        """
        return self._Rmod

    def __repr__(self):
        return "Monoid Sigma_0(%s) x Sigma_0(%s) with coefficients in %s" % (
            self.level(),
            self.level(),
            self.base_ring(),
        )


class Sigma0SquaredElement(MonoidElement):
    r"""
    Class for representing elements of Sigma_0(p)^2.
    """

    def __init__(self, parent, x):
        r"""
        Initialise elements. Input should be pair of elements of
        Sigma_0(p), as given by Pollack's code.

        Input:
                - parent : Sigma0Squared object in which this lives
                - x : tuple of two elements in underlying Sigma0
        """
        ## This is a child of the Sigma0Squared object chosen
        MonoidElement.__init__(self, parent)
        self._val = x
        self._g1 = x[0]
        self._g2 = x[1]

    def first_element(self):
        """
        Returns the first element in the pair.
        """
        return self._g1

    def second_element(self):
        """
        Returns the second element in the pair.
        """
        return self._g2

    def _repr_(self):
        return "(%s,\n%s)" % (self.first_element(), self.second_element())

    def __hash__(self):
        return hash(self._val)


class Sigma0SquaredAction(Action):
    r"""
    Encodes the action of Sigma_0(p) x Sigma_0(p) on distributions.

    BY DEFAULT THIS IS A **RIGHT** ACTION, EXACTLY THE SAME AS P-S ENS PAPER OR CW'S PLMS PAPER
    """

    def __init__(self, Sigma0Squared, D, act_on_left=False):
        r"""
        Input:
                - D : module of Bianchi distributions (BianchiDistributions object)
                - Sigma0Squared : monoid Sigma_0(p)^2 (Sigma0Squared parent object)
                - act_on_left : indicator for right or left action (default False, so right action)
        """
        Action.__init__(self, Sigma0Squared, D, is_left=act_on_left, op=operator.mul)

    def _act_(self, g, mu):
        """
        Returns mu.g, where mu is a Bianchi distribution object and g is a
        Sigma0SquaredElement object

        EXAMPLES::

                sage: from darmonpoints.ocbianchi import BianchiDistributions
                sage: D = BianchiDistributions(11,4)
                sage: mu = D.basis_vector((1,0))
                sage: g = D.Sigma0Squared()([1,-1,0,1],[1,0,0,1])
                sage: mu*g
                X + 1329*X^2 + 3*X^3
                sage: g = D.Sigma0Squared()([1,1,0,1],[1,0,0,1])
                sage: mu*g
                X + 2*X^2 + 3*X^3
                sage: D = BianchiDistributions(11,3)
                sage: mu = D.basis_vector((1,2)) + D.basis_vector((1,0))
                sage: g = D.Sigma0Squared()([1,2,11,3],[1,3,0,4])
                sage: mu*g
                102*X + 45*X^2 + 64*X*Y + 14*X^2*Y + 9*X*Y^2 + 36*X^2*Y^2

        """
        ## Get matrix of g acting on distributions
        matrix_of_action = mu.parent()._get_powers(g)

        ## Get vector corresponding to mu
        vector_mu = mu._moments

        acted_moments = (matrix_of_action * vector_mu).change_ring(
            mu.parent().base_ring()
        )
        return mu.parent()(vector(acted_moments))


##===========================================================================================
##
##                DISTRIBUTION ELEMENTS
##
##===========================================================================================


class BianchiDistributionElement(ModuleElement):
    r"""
    This class represents elements in an overconvergent Bianchi coefficient module.

    INPUT:

     - ``parent`` - An overconvergent coefficient module.

     - ``val`` - The value that it needs to store (default: 0). It can be another BianchiDistributionElement,
       in which case the values are copied. It can also be a column vector (or something
       coercible to a column vector) which represents the values of the element applied to
       the polynomials `1`, `x`, `y`, `x^2`, `xy`, `y^2`, ... ,`y^n`.

     - ``check`` - boolean (default: True). If set to False, no checks are done and ``val`` is
       assumed to be the a column vector.

    """

    def __init__(self, parent, val=0, check=True, normalize=False):
        """
        Initialisation function. Takes as input a vector val, which should have length equal to the
        dimension of the space, which is the nth triangle number, where n is the depth. This corresponds
        to the ordered basis for distributions (namely, the dual basis to the basis 1, x, y, x^2, xy, ...).

        Input:
            - parent: BianchiDistributions object of depth n
            - val : vector of length n^2 encoding the moments of the distribution
        """
        ## Parents/precision
        ModuleElement.__init__(self, parent)
        self._parent = parent
        self._depth = self._parent._depth
        self._dimension = self._parent._dimension

        ## check multiple possibilities for input
        if not check:
            self._moments = val
        else:
            ## is input already a distribution?
            if isinstance(val, self.__class__):
                ## if depth is the same, then keep this
                if val._parent._depth == parent._depth:
                    self._moments = val._moments
                else:
                    ## depths are different, take the minimum
                    d = min([val.nrows(), parent.dimension()])
                    self._moments = val._moments.submatrix(0, 0, nrows=d)

            elif isinstance(val, int) or isinstance(val, Integer):
                ## Initialise distribution to be trivial, i.e. constant moment = input and rest = 0
                self._moments = MatrixSpace(self._parent._R, self._dimension, 1)(0)
                self._moments[0, 0] = val

            ## input is a vector storing the moments
            elif isinstance(val, Vector_integer_dense) or isinstance(
                val, FreeModuleElement_generic_dense
            ):
                self._moments = MatrixSpace(self._parent._R, self._dimension, 1)(0)
                for i, o in enumerate(val.list()):
                    self._moments[i, 0] = o

            ## input is a list storing the moments
            elif isinstance(val, list):
                self._moments = MatrixSpace(self._parent._R, self._dimension, 1)(0)
                for i, o in enumerate(val):
                    self._moments[i, 0] = o
            else:
                try:
                    self._moments = Matrix(self._parent._R, self._dimension, 1, val)
                except (TypeError, ValueError):
                    self._moments = self._parent._R(val) * MatrixSpace(
                        self._parent._R, self._dimension, 1
                    )(1)

    def __hash__(self):
        return hash(self._moments)

    def moment(self, ij):
        """
        Returns the (i,j)th moment mu(x^iy^j).

        EXAMPLES::

            sage: from darmonpoints.ocbianchi import BianchiDistributions
            sage: D = BianchiDistributions(11,4)
            sage: mu = D.basis_vector((2,3))
            sage: mu.moment((2,3))
            1 + O(11^3)
            sage: mu.moment((2,1))
            O(11^3)

        """
        if isinstance(ij, tuple):
            idx = self._parent.index(ij)
        else:
            idx = ij
        return self._parent._Rmod(self._moments[idx, 0])

    def moments(self):
        """
        Returns the moments (as a column vector).

        EXAMPLES::

            sage: from darmonpoints.ocbianchi import BianchiDistributions
            sage: D = BianchiDistributions(11,2)
            sage: mu = D.basis_vector((1,1))
            sage: mu.moments()
            [0]
            [0]
            [0]
            [1]
        """
        return self._moments

    def __getitem__(self, ij):
        r""" """
        return self.moment(ij)

    def __setitem__(self, ij, val):
        r"""
        Sets the value of ``self`` on the polynomial `x^iy^j` to ``val``.

        INPUT:
        - ``r`` - an integer. The power of `x`.
        - ``val`` - a value.

        """
        if isinstance(ij, tuple):
            idx = self._parent.index(ij[0], ij[1])
        else:
            idx = ij
        self._moments[idx, 0] = val

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

    def matrix_rep(self, B=None):
        r"""
        Returns a matrix representation of ``self``.
        """
        # Express the element in terms of the basis B
        if B is None:
            B = self._parent.basis()

        A = Matrix(
            self._parent._R,
            self._parent.dimension(),
            self._parent.dimension(),
            [[b._moments[ii, 0] for b in B] for ii in range(self._dimension)],
        )
        tmp = A.solve_right(self._moments)
        return tmp

    def _add_(self, y):
        r"""
        Add two elements.

        EXAMPLES::

            sage: from darmonpoints.ocbianchi import BianchiDistributions
            sage: D = BianchiDistributions(11,4)
            sage: mu1 = D.basis_vector((2,3))
            sage: mu2 = D.basis_vector((1,2))
            sage: mu1 + mu2
            X*Y^2 + X^2*Y^3

        """
        val = self._moments + y._moments
        return self.__class__(self._parent, val, check=False)

    def _sub_(self, y):
        r"""
        Subtract two elements.
        """
        val = self._moments - y._moments
        return self.__class__(self._parent, val, check=False)

    def _neg_(self):
        return self.__class__(self._parent, -self._moments, check=False)

    def _rmul_(self, a):
        # assume that a is a scalar
        return self.__class__(self._parent, a * self._moments, check=False)

    def _repr_(self):
        r"""
        Returns the representation of self as a string. The monomial X^iY^j is the dual basis vector
        to the monomial x^iy^j in the ring of analytic functions.

        EXAMPLES::

            sage: from darmonpoints.ocbianchi import BianchiDistributions
            sage: D = BianchiDistributions(11,4)
            sage: mu = D.basis_vector((2,1)) + D.basis_vector((1,0))
            sage: mu
            X + X^2*Y
            sage: D.basis_vector((1,1)) + 2*D.basis_vector((2,1))
            X*Y + 2*X^2*Y

        """
        R = self.parent()._repr_R
        s = str(
            sum(
                [
                    ZZ(self._moments[idx, 0]) * self._parent.monomial_from_index(idx, R)
                    for idx in range(self._moments.nrows())
                ]
            )
        )
        return s

    def __eq__(self, other):
        return self._moments == other._moments

    def __nonzero__(self):
        return self._moments != 0

    def evaluate_at_tensor(self, P, Q, R=None, depth=None):
        r"""
        Evaluate ``self`` at a polynomial P(x)Q(y).

        By default, this function picks the ring R to be a ring that coerces to both the
        base ring of the polynomials and the Bianchi distribution.

        You can specify depth, but this currently does nothing at all.

        EXAMPLES::

            sage: from darmonpoints.ocbianchi import BianchiDistributions
            sage: D = BianchiDistributions(11,4)
            sage: x,y = D.analytic_vars()
            sage: mu = D.basis_vector((2,1)) + D.basis_vector((1,0))
            sage: mu(x^2*y)
            1
            sage: mu(y)
            0
            sage: mu(x^2*y + x)
            2
        """
        p = self._parent._p

        ## Currently empty functionality
        if depth is None:
            depth = self._depth

        # Define the ring R, if not specified
        if R is None:
            try:
                R = pushout(P.parent().base_ring(), self.parent().base_ring())
            except AttributeError:
                R = self.parent().base_ring()

        ans = 0
        # tr = lambda o : o._polynomial_list(pad=True)[0]
        for i in range(self._depth):
            for j in range(self._depth):
                new_ans = self[i, j] * P[i] * Q[j]
                ans += new_ans
        return ans

    def evaluate_at_poly(self, P, R=None, depth=None):
        r"""
        Evaluate ``self`` at a polynomial. The polynomial can be defined over ZZ or Zp.

        By default, this function picks the ring R to be a ring that coerces to both the
        base ring of the polynomial and the Bianchi distribution.

        You can specify depth, but this currently does nothing at all.

        EXAMPLES::

            sage: from darmonpoints.ocbianchi import BianchiDistributions
            sage: D = BianchiDistributions(11,4)
            sage: x,y = D.analytic_vars()
            sage: mu = D.basis_vector((2,1)) + D.basis_vector((1,0))
            sage: mu(x^2*y)
            1
            sage: mu(y)
            0
            sage: mu(x^2*y + x)
            2
        """
        p = self._parent._p

        ## Currently empty functionality
        if depth is None:
            depth = self._depth

        # Define the ring R, if not specified
        if R is None:
            try:
                R = pushout(P.parent().base_ring(), self.parent().base_ring())
            except AttributeError:
                R = self.parent().base_ring()

        ## Attempt to coerce the input into a form we can evaluate
        # P = self.parent().analytic_functions()(P)

        ## For each monomial x^iy^j in the polynomial, multip] ly the coefficient of X^iY^j (in mu) by the
        ## coefficient of x^iy^j (in f) and take the sum. This is our final value
        ##          --> P.coefficients is a dictionary which has monomials as keys; we generate monomials using exponents.
        ##         --> self._moments takes as input an index and spits out the cofficient. So generate the index from the exponent.
        coefficient_list = []
        for polx in P.padded_list(self._depth):
            coefficient_list.extend(polx.padded_list(self._depth))
        return ZZ((Matrix(coefficient_list) * self.moments())[0, 0])

    def __call__(self, P):
        r"""
        Call function; evaluates the distribution at an analytic function.
        """
        return self.evaluate_at_poly(P)

    def reduce_mod(self, N=None):
        r"""
        Reduces all the moments modulo N.
        """
        if N is None:
            N = self.parent()._pN
        self._moments = self._moments.apply_map(lambda x: x % N)
        return self

    def max_filtration_step(self):
        r"""
        Computes the maximal step of the filtration in which mu lives.
        """

        ## Take min of v_p(mu(x^i*y^j)) + i + j
        p = self._parent._p
        min_modified_moment = min(
            (
                o[0].valuation(p) + sum(tuple(self.parent().ij_from_pos(n)))
                for n, o in enumerate(self._moments)
            )
        )

        ## Last filtration step in which this appears is step r, where r is the min such that this min/2 - r >= 0
        ## ..... IN THE SUPERSINGULAR CASE!
        ## In the ordinary case, the min r is sufficient *without* dividing by 2!!!
        return min_modified_moment  ## QQ(min_modified_moment/2).floor()

    def normalize(self, r=None):
        r"""
        Adjust the moments to the precision given by the filtration step where self belongs.
        """
        if r is None:
            r = self.max_filtration_step()
        V = self._moments
        p = self._parent._p
        for n in range(self._moments.nrows()):
            k = r - sum(tuple(self.parent().ij_from_pos(n)))
            self._moments[n, 0] = self._moments[n, 0] % p**k
        return self

    def valuation(self):
        r"""
        Returns the same as max_filtration_step, defining an element to have valuation r
        if Filr^(r,r) is the maximal filtration step in which it lives.
        """
        return self.max_filtration_step()


##===========================================================================================
##
##                        DISTRIBUTIONS (PARENT)
##
##===========================================================================================
class BianchiDistributions(Module, UniqueRepresentation):
    r"""
    This class represents the overconvergent approximation modules used to
    describe p-adic overconvergent Bianchi modular symbols.

    INPUT:

     - ``p`` - integer
        Prime with which we work

     - ``depth`` - integer (Default: None)
        Precision to which we work; work with moments x^iy^j for
        i,j up to the depth

     - ``act_on_left`` - boolean, (Default: False)
        Encodes whether Sigma_0(p)^2 is acting on the left or right.

     - ``adjuster`` - Sigma0ActionAdjuster class (Default: _default_adjuster())
        If using a different convention for matrix actions, tell the code where a,b,c,d w
        should be mapped to.


    AUTHORS:

    - Marc Masdeu (2018-08-14)
    - Chris Williams (2018-08-16)
    """

    def __init__(self, p, depth, act_on_left=False, adjuster=None):
        self._dimension = (
            0  ## Hack!! Dimension was being called before it was intialised
        )
        self._Rmod = ZpCA(p, depth - 1)  ## create Zp
        Module.__init__(self, base=self._Rmod)
        self.Element = BianchiDistributionElement
        self._R = ZZ
        self._p = p
        self._depth = depth
        self._pN = self._p ** (depth - 1)
        self._cache_powers = dict()
        self._unset_coercions_used()

        ## Initialise monoid Sigma_0(p) + action; use Pollack-Stevens modular symbol code
        ## our_adjuster() is set above to allow different conventions
        if adjuster is None:
            adjuster = _default_adjuster()

        self._adjuster = adjuster

        ## Power series ring for representing distributions as strings
        self._repr_R = PowerSeriesRing(
            self._R, num_gens=2, default_prec=self._depth, names="X,Y"
        )

        self._Sigma0Squared = Sigma0Squared(self._p, self._Rmod, adjuster)
        self._act = Sigma0SquaredAction(
            self._Sigma0Squared, self, act_on_left=act_on_left
        )
        self.register_action(self._act)
        self._populate_coercion_lists_()

        ## Initialise dictionaries of indices to translate between pairs and index for moments
        self._index = dict()
        self._ij = []
        m = 0

        ## Populate dictionary/array giving index of the basis element corr. to tuple (i,j), 0 <= i,j <= depth = n
        ## These things are ordered by degree of y, then degree of x: [1, x, x^2, ..., y, xy, ... ]
        for j in range(depth):
            for i in range(depth):
                self._ij.append((i, j))
                self._index[(i, j)] = m
                m += 1

        self._dimension = m  ## Number of moments we store

        ## Power series ring Zp[[x,y]]. We have to work with monomials up to x^depth * y^depth, so need prec = 2*depth
        self._PowerSeries_x = PowerSeriesRing(
            self._Rmod, default_prec=self._depth, names="x"
        )
        self._PowerSeries_x_ZZ = PowerSeriesRing(
            ZZ, default_prec=self._depth, names="x"
        )
        self._PowerSeries = PowerSeriesRing(
            self._PowerSeries_x, default_prec=self._depth, names="y"
        )
        self._PowerSeries_ZZ = PowerSeriesRing(
            self._PowerSeries_x_ZZ, default_prec=self._depth, names="y"
        )

    def index(self, ij):
        r"""
        Function to return index of a tuple (i,j).

        Input:
           - ij (tuple) : pair (i,j)
        Returns:
            Place in ordered basis corresponding to x^iy^j.
        """
        return self._index[tuple(ij)]

    def ij_from_pos(self, n):
        r"""
        From position in the ordered basis, returns corr. tuple (n,i)

        Input:
                - n (int) : position in basis.
        Returns:
                pair (i,j) s.t. the nth basis vector is x^iy^j
        """
        return self._ij[n]

    def monomial_from_index(self, n, R=None):
        """
        Takes index and returns the corresponding monomial in the basis
        """
        X, Y = self._repr_R.gens()
        if isinstance(n, tuple):
            (i, j) = n
        else:
            i, j = self._ij[n]
        return X**i * Y**j

    def basis_vector(self, ij):
        """
        Returns the (i,j)th basis vector (in the dual basis), which takes
        the monomial x^iy^j to 1 and every other monomial to 0.

        EXAMPLES::

            sage: from darmonpoints.ocbianchi import BianchiDistributions
            sage: D = BianchiDistributions(11,4)
            sage: D.basis_vector((2,3))
            X^2*Y^3
            sage: D.basis_vector(5)
            X*Y
        """
        moments = vector(ZZ, [0 for i in range(self._dimension)])
        if isinstance(ij, tuple):
            index = self.index(ij)
            moments[index] = 1
        else:
            moments[ij] = 1
        return self(moments)

    def analytic_functions(self):
        r"""
        Returns underlying power series of rigid analytic functions, that is,
        the space on which a distribution should take values.
        """
        return self._PowerSeries

    def analytic_vars(self):
        r"""
        Returns x,y, the variables of the underlying ring of analytic functions.
        """
        x = self.analytic_functions()(self._PowerSeries_x.gen())
        y = self.analytic_functions().gen()
        return x, y

    def Sigma0Squared(self):
        r"""
        Returns underlying monoid Sigma_0(p)^2.
        """
        return self._Sigma0Squared

    def Sigma0(self):
        r"""
        Returns underlying monoid Sigma_0(p)^2.
        """
        return self._Sigma0Squared

    def approx_module(self, M=None):
        if M is None:
            M = self.dimension()
        return MatrixSpace(self._R, M, 1)

    def clear_cache(self):
        del self._cache_powers
        self._cache_powers = dict()

    def is_overconvergent(self):
        return True

    def _an_element_(self):
        r""" """
        return BianchiDistributionElement(
            self,
            Matrix(self._R, self._dimension, 1, range(1, self._dimension + 1)),
            check=False,
        )

    def _coerce_map_from_(self, S):
        # Nothing coherces here, except BianchiDistributionElement
        return False

    def _element_constructor_(self, x, check=True, normalize=False):
        # Code how to coherce x into the space
        # Admissible values of x?
        return BianchiDistributionElement(self, x)

    def acting_matrix(self, g, M):
        G = g.parent()
        try:
            qrep = G.quaternion_to_matrix(g)
            qrep_bar = qrep.apply_map(lambda x: x.trace() - x)
            first, second = qrep.apply_map(G._F_to_local), qrep_bar.apply_map(
                G._F_to_local
            )
        except AttributeError:
            emb0, emb1 = G.embeddings()
            first, second = emb0(g, M), emb1(g, M)
        return self._get_powers(self.Sigma0Squared()(first, second))

    def _get_powers(self, g, emb=None):
        r"""
        Auxiliary function to compute the Sigma_0(p)^2 action on moments.

        The action sends a monomial x^i to (gx)^i, where gx = (b+dx)/(a+cx). The
        action on two-variable functions is simply the product of two copies of the
        one variable action.

        Input:
                - g : Sigma0SquaredElement object (in the relevant Sigma_0(p)^2 group)

        Returns:
                matrix of (g_x,g_y) acting on distributions in the basis given by monomials

        EXAMPLES::

            sage: from darmonpoints.ocbianchi import BianchiDistributions
            sage: D = BianchiDistributions(11,2)
            sage: h = D.Sigma0Squared()([1,1,0,1],[1,1,0,1])
            sage: D._get_powers(h)
            [1 0 0 0]
            [1 1 0 0]
            [1 0 1 0]
            [1 1 1 1]
            sage: h = D.Sigma0Squared()([2,3,11,1],[12,1,22,1])
            sage: D._get_powers(h)
            [1 0 0 0]
            [7 6 0 0]
            [1 0 1 0]
            [7 6 7 6]
        """
        ## We want to ultimately compute actions on distributions. The matrix describing the (left)
        ## action of g on distributions is the transpose of the action of adjoint(g) acting on the (left)
        ## of analytic functions, so we start by taking adjoints. Then put the matrix entries into lists

        ## NOTE: First apply the adjuster defined above; permutes a,b,c,d to allow for different conventions.
        abcdx = g.first_element()
        abcdy = g.second_element()

        ## Adjust for action: change of convention is encoded in our_adjuster class above
        adjuster = self._adjuster
        abcdx = adjuster(abcdx.matrix())
        abcdy = adjuster(abcdy.matrix())

        ## We want better keys; keys in Zp are not great. Store them instead in ZZ
        abcdxZZ = tuple(ZZ(t) for t in abcdx)
        abcdyZZ = tuple(ZZ(t) for t in abcdy)

        ## check to see if the action of (g,h) has already been computed and cached
        try:
            return self._cache_powers[(abcdxZZ, abcdyZZ)]
        except KeyError:
            pass

        ## Sanity check output
        verbose(
            "The element [{},{}] has not been stored. Computing:".format(
                abcdxZZ, abcdyZZ
            ),
            level=2,
        )

        R = self._PowerSeries  ## Zp[[x,y]]
        y = R.gen()
        x = R.base_ring().gen()

        ## get values of a,b,c,d for x and y
        if emb is None:
            a, b, c, d = abcdx
            A, B, C, D = abcdy
        else:
            gg = emb(abcdy)
            a, b, c, d = gg[0].list()
            A, B, C, D = gg[1].list()

        ## Initialise terms
        num_x = b + d * x  ## b + az + O(11^depth)R
        denom_x = a + c * x  ## d + cz + O(11^depth)R
        num_y = B + D * x
        denom_y = A + C * x

        ## Ratios
        r = R.base_ring()(num_x / denom_x)  ## after action on x
        s = num_y / denom_y  ## after action on y

        r = r.change_ring(ZZ)
        s = s.change_ring(ZZ)

        RZ = self._PowerSeries_ZZ
        phi = s.parent().hom([RZ.gen()])
        ## Constant term
        const = r.parent()(1)
        spows = [const]
        for n in range(self._depth):
            spows.append(s * spows[-1])

        acted_monomials = {}
        for j in range(self._depth):
            acted_monomials[(0, j)] = phi(spows[j])
        rpow = 1
        for i in range(1, self._depth):
            rpow *= r
            rpow.add_bigoh(self._depth)
            for j in range(self._depth):
                acted_monomials[(i, j)] = rpow * phi(spows[j])

        matrix_rows = []
        for n in range(self._dimension):
            f = acted_monomials[tuple(self.ij_from_pos(n))]
            new_row = []
            for polx in f.padded_list(self._depth):
                new_row.extend(polx.padded_list(self._depth))
            matrix_rows.append(new_row)

        ## Build matrix . DO NOT TAKE TRANSPOSE, (built this in as a consequence of implementation)
        matrix_action = Matrix(ZZ, matrix_rows)
        # acted_monomials_list = Matrix(R.base_ring(),self._depth,self._depth,acted_monomials_list)#.apply_map(ZZ)
        self._cache_powers[(abcdxZZ, abcdyZZ)] = matrix_action
        return matrix_action

    def _repr_(self):
        r"""
        This returns the representation of self as a string.
        """
        return (
            "Space of %s-adic Bianchi distributions with k=0 action and precision cap %s"
            % (self._p, self._dimension - 1)
        )

    def prime(self):
        r"""
        Returns underlying prime.
        """
        return self._p

    def basis(self):
        r"""
        A basis of the module.

        Returns all monomials in x,y of degree (in each variable) up to the specified depth-1.

        """
        try:
            return self._basis
        except:
            pass
        self._basis = [
            BianchiDistributionElement(
                self,
                Matrix(self._R, self._dimension, 1, {(jj, 0): 1}, sparse=False),
                check=False,
            )
            for jj in range(self._dimension)
        ]
        return self._basis

    def base_ring(self):
        r"""
        This function returns the base ring of the overconvergent element.
        """
        return self._Rmod

    def depth(self):
        r"""
        Returns the depth of the module. If the depth is d, then a basis for the approximation
        modules is x^iy^j with i,j in {0,...,d-1}.
        """
        return self._depth

    def dimension(self):
        r"""
        Returns the dimension (rank) of the module.
        """
        return self._dimension

    def precision_cap(self):
        r"""
        Returns the depth of the module. If the depth is d, then a basis for the approximation
        modules is x^iy^j with i,j in {0,...,d-1}.
        """
        return self._depth

    def is_exact(self):
        r"""
        All distributions are finite approximations. They are only exact as elements of
        D/Fil^{d,d}D, where d is the depth.
        """
        return False
