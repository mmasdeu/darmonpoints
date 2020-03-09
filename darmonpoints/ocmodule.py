#########################################################################
#       Copyright (C) 2011 Cameron Franc and Marc Masdeu
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#                  http://www.gnu.org/licenses/
#########################################################################
from sage.structure.element import ModuleElement
from sage.modules.module import Module
from sage.matrix.constructor import Matrix
from sage.matrix.matrix_space import MatrixSpace
from sage.rings.finite_rings.integer_mod_ring import Zmod
from sage.rings.all import Integer,Zp
from sage.rings.padics.factory import ZpCA
from sage.rings.power_series_ring import PowerSeriesRing
from sage.structure.unique_representation import UniqueRepresentation
from sage.rings.rational_field import QQ
from sage.rings.integer_ring import ZZ
from sage.rings.padics.padic_generic import pAdicGeneric
from sage.categories.pushout import pushout
from sage.rings.infinity import Infinity
from sage.structure.richcmp import richcmp
from sage.structure.sage_object import load,save
from sage.structure.unique_representation import CachedRepresentation
from sage.categories.action import Action
from sage.structure.parent import Parent
from sage.modular.pollack_stevens.sigma0 import Sigma0,Sigma0ActionAdjuster
from sage.modules.vector_integer_dense import Vector_integer_dense
from sage.modules.free_module_element import FreeModuleElement_generic_dense
from sage.misc.cachefunc import cached_method
from .homology import MatrixAction, Scaling, Divisors
import operator

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
        a,b,c,d = g.list()
        return tuple([d,b,c,a])

class ps_adjuster(Sigma0ActionAdjuster):
    """
    Callable object that turns matrices into 4-tuples.

    """
    def __call__(self, g):
        a,b,c,d = g.list()
        return tuple([a,-b,-c,d])

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
    def __init__(self,parent,val = 0,check = True,normalize=False):
        ModuleElement.__init__(self,parent)
        self._parent = parent
        self._depth = self._parent._depth
        if not check:
            self._val = val
        else:
            if isinstance(val,self.__class__):
                if val._parent._depth == parent._depth:
                    self._val = val._val
                else:
                    d = min([val._parent._depth,parent._depth])
                    self._val = val._val.submatrix(0,0,nrows = d)

            elif isinstance(val, Vector_integer_dense) or isinstance(val, FreeModuleElement_generic_dense):
                self._val = MatrixSpace(self._parent._R, self._depth, 1)(0)
                for i,o in enumerate(val.list()):
                    self._val[i,0] = o
            else:
                try:
                    self._val = Matrix(self._parent._R,self._depth,1,val)
                except (TypeError, ValueError):
                    self._val= self._parent._R(val) * MatrixSpace(self._parent._R,self._depth,1)(1)
        self._moments = self._val

    def lift(self, p=None,M=None):
        return self

    def moment(self, i):
        return self._parent._Rmod(self._moments[i,0])

    def __getitem__(self,r):
        r"""
        Returns the value of ``self`` on the polynomial `x^r`.

        INPUT:
          - ``r`` - an integer. The power of `x`.

        EXAMPLES:

        """
        return self._val[r,0]

    def __setitem__(self,r, val):
        r"""
        Sets the value of ``self`` on the polynomial `x^r` to ``val``.

        INPUT:
        - ``r`` - an integer. The power of `x`.
        - ``val`` - a value.

        EXAMPLES:

        """
        self._val[r,0] = val

    def element(self):
        r"""
        The element ``self`` represents.
        """
        tmp = self.matrix_rep()
        return [tmp[ii,0] for ii in range(tmp.nrows())]

    def list(self):
        r"""
        The element ``self`` represents.
        """
        return self.element()

    def matrix_rep(self,B=None):
        r"""
        Returns a matrix representation of ``self``.
        """
        #Express the element in terms of the basis B
        if B is None:
            B = self._parent.basis()
        A=Matrix(self._parent._R,self._parent.dimension(),self._parent.dimension(),[[b._val[ii,0] for b in B] for ii in range(self._depth)])
        tmp=A.solve_right(self._val)
        return tmp

    def _add_(self,y):
        r"""
        Add two elements.
        """
        val=self._val+y._val
        return self.__class__(self._parent,val, check = False)

    def _sub_(self,y):
        r"""
        Subtract two elements.
        """
        val=self._val-y._val
        return self.__class__(self._parent,val, check = False)

    def _div_(self,right):
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
            assert (self - a * right).is_zero(), 'Not a scalar multiple of right'
            return a

    def r_act_by(self,x):
        r"""
        Act on the right by a matrix.
        """
        #assert(x.nrows()==2 and x.ncols()==2) #An element of GL2
        return self._acted_upon_(x.adjugate(), False)

    def _acted_upon_(self,x, right_action): # Act by x on the left
        try:
            x = x.matrix()
        except AttributeError: pass
        if right_action:
            return self._acted_upon_(x.adjugate(), False)
        else:
            R = self._parent._R
            A = self._parent._get_powers(x)
            tmp = A * self._val
            return self.__class__(self._parent, tmp, check = False)

    def _neg_(self):
        return self.__class__(self._parent,-self._val, check = False)

    def _rmul_(self,a):
        #assume that a is a scalar
        return self.__class__(self._parent,self._parent._Rmod(a)*self._val, check = False)

    def _repr_(self):
        r"""
        Returns the representation of self as a string.
        """
        R = PowerSeriesRing(self._parent._R,default_prec=self._depth,name='z')
        z = R.gen()
        s = str(sum([R(self._val[ii,0]*z**ii) for ii in range(self._depth)]))
        return s

    def _cmp_(self,other):
        return (self._val > other._val) - (self._val < other._val)

    def __nonzero__(self):
        return self._val!=0

    def evaluate_at_poly(self,P,R = None,depth = None):
        r"""
        Evaluate ``self`` at a polynomial
        """
        p = self._parent._p
        if R is None:
            try:
                R = pushout(P.parent().base_ring(),self.parent().base_ring())
            except AttributeError:
                R = self.parent().base_ring()
        if depth is None and hasattr(P,'degree'):
            try:
                depth = min([P.degree()+1,self._depth])
                return sum(R(self._val[ii,0])*P[ii] for ii in range(depth))
            except NotImplementedError: pass
            return R(self._val[0,0])*P
        else:
            return sum(R(self._val[ii,0])*P[ii] for ii in range(self._depth))

    def valuation(self,l=None):
        r"""
        The `l`-adic valuation of ``self``.

        INPUT: a prime `l`. The default (None) uses the prime of the parent.

        """
        if not self._parent.base_ring().is_exact():
            if(not l is None and l!=self._parent._Rmod.prime()):
                raise ValueError("This function can only be called with the base prime")
            l = self._parent._Rmod.prime()
            return min([self._val[ii,0].valuation(l) for ii in range(self._depth)])
        else:
            return min([self._val[ii,0].valuation(l) for ii in range(self._depth)])

    def valuation_list(self,l=None):
        r"""
        The `l`-adic valuation of ``self``, as a list.

        INPUT: a prime `l`. The default (None) uses the prime of the parent.

        """
        if not self._parent.base_ring().is_exact():
            if(not l is None and l!=self._parent._Rmod.prime()):
                raise ValueError("This function can only be called with the base prime")
            l = self._parent._Rmod.prime()
            return [self._val[ii,0].valuation(l) for ii in range(self._depth)]
        else:
            return [self._val[ii,0].valuation(l) for ii in range(self._depth)]

    def reduce_mod(self, N = None):
        if N is None:
            N = self.parent()._pN
        self._val = self._val.apply_map(lambda x: x % N)
        return self


class OCVn(Module,UniqueRepresentation):
    Element=OCVnElement
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
    def __init__(self,p,depth):
        Module.__init__(self,base = Zmod(p**(depth-1)))
        self._R = Zmod(p**(depth-1))
        self._p = p
        self._Rmod = ZpCA(p,depth - 1)
        self._depth = depth
        self._pN = self._p**(depth - 1)
        self._PowerSeries = PowerSeriesRing(self._Rmod, default_prec = self._depth,name='z')
        self._cache_powers = dict()
        self._unset_coercions_used()
        self._Sigma0 = Sigma0(self._p, base_ring = self._Rmod, adjuster = our_adjuster())
        self.register_action(Sigma0Action(self._Sigma0,self))
        self._populate_coercion_lists_()

    def Sigma0(self):
        return self._Sigma0

    def approx_module(self, M = None):
        if M is None:
            M = self._depth
        return MatrixSpace(self._R, M, 1)

    def clear_cache(self):
        del self._cache_powers
        self._cache_powers = dict()

    def is_overconvergent(self):
        return True

    def _an_element_(self):
        r"""
        """
        return OCVnElement(self,Matrix(self._R,self._depth,1,range(1,self._depth+1)), check = False)

    def _coerce_map_from_(self, S):
        # Nothing coherces here, except OCVnElement
        return False

    def _element_constructor_(self,x,check = True,normalize=False):
        #Code how to coherce x into the space
        #Admissible values of x?
        return OCVnElement(self, x)

    def acting_matrix(self, g, M):
        try:
            g = g.matrix()
        except AttributeError: pass
        return self._get_powers(g).submatrix(0,0,M,M)

    def _get_powers(self,abcd,emb = None):
        abcd = tuple(abcd.list())
        try:
            return self._cache_powers[abcd]
        except KeyError:
            pass
        R = self._PowerSeries
        if emb is None:
            a,b,c,d = abcd
        else:
            a,b,c,d = emb(abcd).list()
        r = R([b,a])
        s = R([d,c])
        ratio = r * s**-1
        y = R.one()
        xlist = [[1] + [0 for o in range(self._depth - 1)]]
        for ii in range(1,self._depth):
            y *= ratio
            ylist = y.list()[:self._depth]
            ylist.extend([R.base_ring().zero() for o in range(self._depth - len(ylist))])
            xlist.append([ZZ(o) for o in ylist])
        # x = Matrix(R.base_ring(),self._depth,self._depth, xlist).apply_map(ZZ)
        x = Matrix(ZZ,self._depth,self._depth, xlist)
        self._cache_powers[abcd] = x
        return x

    def _repr_(self):
        r"""
        This returns the representation of self as a string.
        """
        return "Space of %s-adic distributions with k=0 action and precision cap %s"%(self._p, self._depth - 1)

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
        try: return self._basis
        except: pass
        self._basis=[OCVnElement(self,Matrix(self._R,self._depth,1,{(jj,0):1},sparse=False),check = False) for jj in range(self._depth)]
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
    def __init__(self,G,M):
        Action.__init__(self,G,M,is_left = True,op = operator.mul)

    def _act_(self,g,v):
        return v._acted_upon_(g.matrix(), False)

class MeromorphicFunctionsElement(ModuleElement):
    def __init__(self, parent, data, check=True):
        if check:
            additive = parent.is_additive()
            K = parent.base_ring()
            prec = parent._prec
            p = K.prime()
            Ps = parent._Ps
            phi = parent._Ps_local_variable
            if data == 0:
                self._value = parent._V(0) if additive else Ps(1)
            elif isinstance(data.parent(), Divisors):
                self._value = parent._V(0) if additive else Ps(1)
                for Q, n in data:
                    if Q.valuation() >= 0:
                        raise ValueError('Divisor is not defined over the right open')
                    if additive:
                        if parent._dlog:
                            self._value += n * parent._V([o._polynomial_list(pad=True) for o in (phi(K(Q)).log().derivative()).list()])
                        else:
                            self._value += n * parent._V([o._polynomial_list(pad=True) for o in (phi(K(Q)).log()).list()])
                    else:
                        self._value *= phi(K(Q))**n
            elif data.parent() == parent._V:
                self._value = parent._V(data)
            elif hasattr(data,'nrows'): # A matrix
                assert additive
                self._value = parent._V(data)
            else:
                val = Ps(data)
                val.add_bigoh(prec)
                if additive:
                    self._value = parent._V([o._polynomial_list(pad=True) for o in val.list()])
                else:
                    self._value = val
        else:
            self._value = data
        # assert min([o.valuation() for o in self._value.list()]) >= 0
        self._moments = self._value
        ModuleElement.__init__(self,parent)

    def __call__(self, D):
        K = self.parent().base_ring()
        p = K.prime()
        assert isinstance(D.parent(), Divisors) and D.degree() == 0
        if self.parent().is_additive():
            poly = self.parent()._Ps([K(o.list()) for o in self._value.rows()]).polynomial()
            if self.parent()._dlog:
                poly = poly.integral()
            ans = K(0)
            for P, n in D:
                ans += n * poly(P)
            if ans == 0:
                return K(1)
            else:
                return ans.exp()
        else:
            poly = self._value.polynomial()
            ans = K(1)
            for P, n in D:
                assert P.valuation() >= 0
                ans *= (poly(P))**n
            return ans

    def _cmp_(self, right):
        return (self._value > right._value) - (self._value < right._value)

    def valuation(self, p=None):
        K = self.parent().base_ring()
        if self.parent().is_additive():
            return min([Infinity] + [K(o.list()).valuation(p) for o in self._value.rows()])
        else:
            return min([Infinity] + [o.valuation(p) for o in (self._value-1).coefficients()])

    def _add_(self, right):
        if self.parent().is_additive():
            ans = self._value + right._value
        else:
            ans = self._value * right._value
        return self.__class__(self.parent(), ans, check=False)

    def _sub_(self, right):
        if self.parent().is_additive():
            ans = self._value - right._value
        else:
            ans = self._value / right._value
        return self.__class__(self.parent(), ans, check=False)

    def _neg_(self):
        if self.parent().is_additive():
            ans = -self._value
        else:
            ans = self._value**-1
        return self.__class__(self.parent(), ans, check=False)

    def _repr_(self):
        return repr(self._value)

    def scale_by(self, k):
        if self.parent().is_additive():
            ans = k * self._value
        else:
            ans = self._value**k
        return self.__class__(self.parent(), ans, check=False)

    def left_act_by_matrix(self, g): # meromorphic functions
        Ps = self._value.parent()
        K = Ps.base_ring()
        # Below we code the action which is compatible with the usual action
        # P |-> (aP+b)/(cP+D)
        if self.parent().is_additive():
            M = self.parent().get_action_data(g)
            ans = M * self._value
            if not self.parent()._dlog:
                ans[0,0] = 0
                ans[0,1] = 0
        else:
            zz_ps_vec = self.parent().get_action_data(g)
            poly = self._value.polynomial()
            ans = sum(a * zz_ps_vec[e].change_ring(K) for a, e in zip(poly.coefficients(), poly.exponents()))
            ans.add_bigoh(self.parent()._prec)
            ans /= ans[0]
        return self.__class__(self.parent(),ans,check=False)

class MeromorphicFunctions(Parent, CachedRepresentation):
    Element = MeromorphicFunctionsElement
    def __init__(self, K, additive = True, dlog = True):
        Parent.__init__(self)
        self._additive = additive
        self._dlog = dlog
        self._base_ring = K
        self._prec = K.precision_cap()
        psprec = self._prec + 1 if dlog else self._prec
        self._Ps = PowerSeriesRing(self._base_ring, names='t', default_prec=psprec)
        if self._additive:
            self._V = MatrixSpace(Zmod(K.prime()**self._prec), self._prec, 2)
        t = self._Ps.gen()
        self._Ps_local_variable = lambda Q : 1 - t / Q
        self._unset_coercions_used()
        self.register_action(Scaling(ZZ,self))
        self.register_action(MatrixAction(MatrixSpace(K,2,2),self))

    def acting_matrix(self, g, dim=None):
        try:
            g = g.matrix()
        except AttributeError:
            pass
        return self.get_action_data(g)

    @cached_method
    def get_action_data(self, g, K = None):
        a, b, c, d = g.list()
        prec = self._prec
        if K is None:
            if hasattr(a, 'lift'):
                a_inv = (a**-1).lift()
                a, b, c, d = a.lift(), b.lift(), c.lift(), d.lift()
                p = g.parent().base_ring().prime()
                K = Zmod(p**prec)
            else:
                a_inv = a**-1
                K = g.parent().base_ring()

        Ps = PowerSeriesRing(K,'t', default_prec=prec)
        z = Ps.gen()
        denom = a_inv * (-c * a_inv * z + 1)**-1
        zz = (d * z - b) * denom
        zz_ps0 = Ps(zz).add_bigoh(prec)
        if self._dlog:
            zz_ps = ((a*d - b*c) * denom**2).add_bigoh(prec)
        else:
            zz_ps = Ps(1).add_bigoh(prec)
        if self.is_additive():
            M = Matrix(ZZ, prec, prec, 0)
            for j in range(prec):
                for i, aij in enumerate(zz_ps.list()):
                    M[i, j] = aij
                if j < prec - 1: # Don't need the last multiplication
                    zz_ps = (zz_ps0 * zz_ps).add_bigoh(prec)
                else:
                    return M
        else:
            ans = [Ps(1), zz_ps]
            for _ in range(prec - 1):
                zz_ps = (zz_ps0 * zz_ps).add_bigoh(prec)
                ans.append(zz_ps)
            return ans

    def is_additive(self):
        return self._additive

    def base_ring(self):
        return self._base_ring

    def power_series_ring(self):
        return self._Ps

    def _element_constructor_(self, data):
        return self.element_class(self, data)

    def _repr_(self):
        return "Meromorphic %s Functions over %s"%('Additive' if self._additive else 'Multiplicative', self._base_ring)
