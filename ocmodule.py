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
from copy import copy
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
from sage.structure.sage_object import load,save
load('fmpz_mat.spyx')

oo = Infinity

use_fmpz_mat = True

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
    def __init__(self,parent,val = 0,check = False):
        ModuleElement.__init__(self,parent)
        self._parent = parent
        self._depth = self._parent._depth
        if check:
            if isinstance(val,self.__class__):
                if val._parent._depth == parent._depth:
                    self._val = val._val
                else:
                    d = min([val._parent._depth,parent._depth])
                    if use_fmpz_mat:
                        self._val = Fmpz_mat(None,d,1)
                        for i in range(d):
                            self._val[i,0] = val._val[i,0]
                    else:
                        self._val = val._val.submatrix(0,0,nrows = d)
            else:
                try:
                    self._val = Matrix(self._parent._R,self._depth,1,val)
                except:
                    self._val= self._parent._R(val) * MatrixSpace(self._parent._R,self._depth,1)(1)
                if use_fmpz_mat:
                    self._val = Fmpz_mat(self._val)
        else:
            self._val= val
        self.moments = self._val

    def moment(self, i):
        return self.moments[i,0]

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

        EXAMPLES:

        This example illustrates ...

        ::
        """
        tmp = self.matrix_rep()
        return [tmp[ii,0] for ii in range(tmp.nrows())]

    def list(self):
        r"""
        EXAMPLES:

        This example illustrates ...

        ::
        """
        return self.element()

    def matrix_rep(self,B=None):
        r"""

        EXAMPLES:

        This example illustrates ...

        ::

        """
        #Express the element in terms of the basis B
        if B is None:
            B = self._parent.basis()
        A=Matrix(self._parent._R,self._parent.dimension(),self._parent.dimension(),[[b._val[ii,0] for b in B] for ii in range(self._depth)])
        tmp=A.solve_right(self._val)
        return tmp

    def _add_(self,y):
        r"""

        EXAMPLES:

        This example illustrates ...

        ::
        """
        val=self._val+y._val
        return self.__class__(self._parent,val, check = False)

    def _sub_(self,y):
        r"""

        EXAMPLES:

        This example illustrates ...

        ::
        """
        val=self._val-y._val
        return self.__class__(self._parent,val, check = False)

    def r_act_by(self,x):
        r"""

        EXAMPLES:

        This example illustrates ...

        ::
        """
        #assert(x.nrows()==2 and x.ncols()==2) #An element of GL2
        return self._l_act_by(x.adjoint())

    def l_act_by(self,x):
        r"""

        EXAMPLES:

        This example illustrates ...

        ::

        """
        R = self._parent._R
        xdet = x.determinant()

        x.set_immutable()
        tmp = self._parent._get_powers(x) * self._val
        return self.__class__(self._parent, tmp,check = False)

    def _neg_(self):
        r"""

        EXAMPLES:

        This example illustrates ...

        ::

        """
        return self.__class__(self._parent,-self._val, check = False)


    def _rmul_(self,a):
        r"""

        EXAMPLES:

        This example illustrates ...

        ::

        """
        #assume that a is a scalar
        return self.__class__(self._parent,a*self._val, check = False)

    def _repr_(self):
        r"""
        This returns the representation of self as a string.

        EXAMPLES:

        This example illustrates ...

        ::

        """
        R = PowerSeriesRing(self._parent._R,default_prec=self._depth,name='z')
        z = R.gen()
        s = str(sum([R(self._val[ii,0]*z**ii) for ii in range(self._depth)]))
        return s

    def __cmp__(self,other):
        r"""

        EXAMPLES:

        This example illustrates ...

        ::

        """
        return cmp(self._val,other._val)

    def __nonzero__(self):
        r"""

        EXAMPLES:

        This example illustrates ...

        ::
        """
        return self._val!=0

    def evaluate_at_poly(self,P,R = None):
        r"""

        EXAMPLES:

        This example illustrates ...

        ::

        """
        p = self._parent._p
        if R is None:
            try:
                R = pushout(P.parent().base_ring(),self.parent().base_ring())
            except AttributeError:
                R = self.parent().base_ring()

        if hasattr(P,'degree'):
            try:
                r = min([P.degree()+1,self._depth])
                return sum([R(self._val[ii,0])*P[ii] for ii in range(r)])
            except NotImplementedError: pass
        return R(self._val[0,0])*P

    def valuation(self,l=None):
        r"""

        EXAMPLES:

        This example illustrates ...

        ::

        """
        if not self._parent.base_ring().is_exact():
            if(not l is None and l!=self._parent._R.prime()):
                raise ValueError, "This function can only be called with the base prime"
            return min([self._val[ii,0].valuation() for ii in range(self._depth)])
        else:
            return min([self._val[ii,0].valuation(l) for ii in range(self._depth)])


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
        Module.__init__(self,base = ZZ)
        self._R = ZZ
        self._p = p
        self._Rmod = ZpCA(p,depth - 1)
        self._depth = depth
        self._PowerSeries = PowerSeriesRing(self._Rmod, default_prec = self._depth,name='z')
        self._cache_powers = dict()
        self._populate_coercion_lists_()

    def clear_cache(self):
        del self._cache_powers
        self._cache_powers = dict()

    def is_overconvergent(self):
        return True

    def _an_element_(self):
        r"""
        """
        if use_fmpz_mat:
            return OCVnElement(self,Fmpz_mat(Matrix(self._R,self._depth,1,range(1,self._depth+1))), check = False)
        else:
            return OCVnElement(self,Matrix(self._R,self._depth,1,range(1,self._depth+1)), check = False)

    def _coerce_map_from_(self, S):
        r"""

        EXAMPLES:

        ::

        """
        # Nothing coherces here, except OCVnElement
        return False

    def _element_constructor_(self,x,check = True):
        r"""

        EXAMPLES:

        """
        #Code how to coherce x into the space
        #Admissible values of x?
        return OCVnElement(self,x,check)

    def _get_powers(self,abcd,emb = None):
        r"""
        Compute the action of a matrix on the basis elements.

        EXAMPLES:

        ::

        """
        try:
            return self._cache_powers[abcd]
        except KeyError:
            pass
        if emb is None:
            a,b,c,d = abcd.list()
        else:
            a,b,c,d = emb(abcd).list()
        #a,b,c,d = a.lift(),b.lift(),c.lift(),d.lift()
        R = self._PowerSeries
        r = R([b,a])
        s = R([d,c])
        ratio = r * s**-1
        y = R(1)
        if use_fmpz_mat:
            x = Fmpz_mat(None,self._depth,self._depth)
        else:
            x = Matrix(ZZ,self._depth,self._depth,0)
        for jj in range(self._depth):
            x[0,jj] = y[jj]
        for ii in range(1,self._depth):
            y *= ratio
            for jj in range(self._depth):
                x[ii,jj] = y[jj]
        self._cache_powers[abcd] = x
        return x

    def _repr_(self):
        r"""
        This returns the representation of self as a string.

        EXAMPLES:

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

        OUTPUT:

        integer -- the ...

        EXAMPLES:


        """
        try: return self._basis
        except: pass
        if use_fmpz_mat:
            self._basis=[OCVnElement(self,Fmpz_mat(Matrix(self._R,self._depth,1,{(jj,0):1},sparse=False)),check = False) for jj in range(self._depth)]
        else:
            self._basis=[OCVnElement(self,Matrix(self._R,self._depth,1,{(jj,0):1},sparse=False),check = False) for jj in range(self._depth)]
        return self._basis

    def base_ring(self):
        r"""
        This function returns the base ring of the overconvergent element.

        EXAMPLES::

        This example illustrates ...

        ::

        """
        return self._R

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
