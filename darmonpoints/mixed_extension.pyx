from sage.categories.fields import Fields
from sage.rings.all import QQ
from sage.rings.integer_ring import Z as ZZ
from sage.rings.padics.padic_generic import pAdicGeneric
from sage.rings.ring import Field
from sage.structure.element import Element, FieldElement
from sage.structure.richcmp import richcmp
from sage.structure.unique_representation import UniqueRepresentation

from .util import our_sqrt

cimport cython
from cpython.list cimport *
from cpython.number cimport *
from cpython.ref cimport *

from bisect import bisect_left as bisect
from math import atan as atan

from sage.matrix.constructor import Matrix
from sage.rings.all import (
    AA,
    QQ,
    RR,
    ZZ,
    ComplexField,
    NumberField,
    PolynomialRing,
    Qp,
    QuadraticField,
    RealField,
)


def get_word_rep_fast(self, delta, Pold=None):
    cdef int realprec = 800
    cdef int ii = 0
    cdef int i = 0
    cdef int j = 0
    cdef int ji = 0
    cdef int oldji = 0

    cdef list gammas = self.gquats
    cdef list gammas_inv = [None] + [o.conjugate() for o in gammas[1:]]
    cdef list translate_inv = self.translate_inv

    cdef int ngquats = self.ngquats
    cdef list fdargs = self.fdargs
    cdef list findex = self.findex
    cdef list ans = []
    cdef list newcs = []
    cdef B = delta.parent()

    cdef CC = ComplexField(realprec)
    cdef RR = RealField(realprec)
    cdef z0 = CC(0)
    cdef z1 = CC(0)
    cdef a = RR(0)
    cdef b = RR(0)
    cdef c = RR(0)
    cdef d = RR(0)
    cdef P = CC(0,.9)
    cdef x = P
    cdef y = P.parent()(1)
    cdef list embgammas_tw = self.get_embgquats_twisted(P)
    cdef list embgammas = self.embgquats
    cdef float az0 = 0

    cdef float twopi = 2 * float(self.pi)
    Pconj = P.conjugate()
    mats = self._splitting_at_infinity(realprec)
    phi = self.F_into_RR
    emb = lambda q : phi(q[0]) + phi(q[1]) * mats[1] + phi(q[2]) * mats[2] + phi(q[3]) * mats[3]
    embgg = emb(delta)
    while not delta.is_one():
        if (-delta).is_one():
            delta = B.one()
            break
        x, y = embgg[0,0]*x+embgg[0,1]*y, embgg[1,0]*x+embgg[1,1]*y
        az0 = float((x - P*y).argument()) - float((x-Pconj*y).argument())
        while az0 < 0 :
            az0 += twopi
        while az0 > twopi:
            az0 -= twopi
        if az0 > fdargs[-1]: # LESS COMMON
            z1 = x / y
            z0 = (z1 - P) / (z1 - Pconj)
            ji = findex[0]
            a,b,c,d = embgammas_tw[ji]
            if ((a*z0+b)/(c*z0+d)).abs() > z0.abs():
                ji = findex[1]
        else: # COMMON
            ji = findex[bisect(fdargs, az0) + 1]
        if ji == -oldji: # VERY RARE
            a,b,c,d = embgammas_tw[ji]
            z0 = (a*z0+b)/(c*z0+d)
            ii = -ngquats
            while ii <= ngquats:
                if ii == 0:
                    continue
                if ii + ji != 0:
                    a,b,c,d = embgammas_tw[ii]
                    if ((a*z0+b)/(c*z0+d)).abs() < z0.abs():
                        ji = ii
                        break
                    else:
                        ii += 1
        if ji > 0:
            gg = gammas[ji]
            embgg = embgammas[ji]
            newcs = self.translate[ji]
        else:
            gg = gammas_inv[-ji]
            embgg = embgammas[-ji].adjugate()
            newcs = translate_inv[-ji]
        delta = gg * delta
        oldji = ji
        ans.extend(newcs)
    return ans


class QuadExtElement(FieldElement):
    def __init__(self, parent, x, y = None, check = True):
        self._p = parent._p
        if parent is None:
            raise ValueError("The parent must be provided")
        if not check:
            self._a, self._b = x
        else:
            B = parent.base()
            if y is None:
                self._a, self._b = B(x), B.zero()
            else:
                self._a, self._b = B(x), B(y)
        FieldElement.__init__(self, parent)

    # Needed for the class
    def _repr_(self):
        return '%s + ( %s )*pi'%(self._a, self._b)

    def __nonzero__(self):
        return self._a.__nonzero__() or self._b.__nonzero__()

    def list(self):
        return [self._a,self._b]

    # Arithmetic
    def _add_(self, right):
        return self.__class__(self.parent(), (self._a+right._a, self._b+right._b), check = False)

    def _sub_(self, right):
        return self.__class__(self.parent(), (self._a-right._a, self._b-right._b), check = False)

    def _neg_(self):
        return self.__class__(self.parent(), (-self._a, -self._b), check = False)

    def _rmul_(self, right):
        r'''
        We assume that right is in the base of self.parent()
        '''
        return self.__class__(self.parent(), (right * self._a, right * self._b), check=False)

    def _lmul_(self, right):
        r'''
        We assume that right is in the base of self.parent()
        '''
        return self.__class__(self.parent(), (right * self._a, right * self._b), check=False)

    def _mul_(self, right):
        r, s = self.parent()._rs
        ac = self._a*right._a
        bd = self._b*right._b
        ab_times_cd = (self._a+self._b)*(right._a+right._b)
        if r is None:
            return self.__class__(self.parent(),(ac - bd*s, ab_times_cd - (ac + bd)), check = False)
        else:
            return self.__class__(self.parent(),(ac - bd*s, ab_times_cd - ac - bd + bd*r), check = False)

    def sqrt(self, return_all=False):
        r, s = self.parent()._rs
        a, b = self._a, self._b
        base = self.parent().base()
        if return_all:
            raise NotImplementedError
        if r is None:
            if b == 0:
                try:
                    ans = self.__class__(self.parent(), (our_sqrt(a),base.zero()), check=False)
                except ValueError:
                    ans = self.__class__(self.parent(), (base.zero(),our_sqrt(base(-a*s))/s), check=False)
            else:
                ans = our_sqrt(self, return_all = False)
                sqrtnrm = our_sqrt(base(self.norm_relative()))
                try:
                    x = our_sqrt(base((a + sqrtnrm) / 2))
                except ValueError:
                    x = our_sqrt(base((a - sqrtnrm) / 2))
                if x != 0:
                    y = base(b/(2*x))
                    ans = self.__class__(self.parent(), (x, y), check=False)
                else:
                    ans = our_sqrt(self, return_all = False)
        else:
            ans = our_sqrt(self, return_all = False)
        return ans

    def norm_relative(self):
        r, s = self.parent()._rs
        c, d = self._a, self._b
        if r is None:
            return self.parent().base()(c*c + d*d*s)
        else:
            return self.parent().base()(c*c + c*d*r + d*d*s)


    def _div_(self, right):
        a, b = self._a, self._b
        c, d = right._a, right._b
        r, s = self.parent()._rs
        if r is None:
            den = c*c + d*d*s
            return self.__class__(self.parent(), ((a*c+b*d*s) / den, (b*c-a*d) / den), check = False)
        else:
            den = c*c + c*d*r + d*d*s
            return self.__class__(self.parent(), ((a*c+a*d*r+b*d*s) / den, (b*c-a*d) / den), check = False)


    def _richcmp_(self, right, op):
        return richcmp((self._a, self._b), (right._a, right._b), op)
    __richcmp__ = _richcmp_

    def valuation(self, p = None):
        return min([2 * self._a.valuation(p), 2 * self._b.valuation(p) + 1])

    def ordp(self, p = None):
        return self.valuation(p) / 2

    def trace_relative(self):
        parent = self.parent()
        base = parent.base()
        r = parent._rs[0]
        if r is None:
            return parent.relative_degree()*base(self._a)
        else:
            return parent.relative_degree()*base(self._a) + base(self._b) * base(r)

    def trace_absolute(self):
        y = self.trace_relative()
        if hasattr(y,'trace'):
            return y.trace()
        else:
            return y.trace_absolute()

class QuadExt(UniqueRepresentation, Field): # Implement extension by x^2 - r*x + s
    r"""
    A quadratic extension of a p-adic field.

    EXAMPLES::

        sage: from darmonpoints.mixed_extension import *
        sage: p = 7
        sage: K0.<z> = Qq(p**2,20)
        sage: K = QuadExt(K0, p)
        sage: print(K(3) + K(5))
        1 + 7 + O(7^20) + ( 0 )*pi
        sage: print(K(3) - K(5))
        5 + 6*7 + 6*7^2 + 6*7^3 + 6*7^4 + 6*7^5 + 6*7^6 + 6*7^7 + 6*7^8 + 6*7^9 + 6*7^10 + 6*7^11 + 6*7^12 + 6*7^13 + 6*7^14 + 6*7^15 + 6*7^16 + 6*7^17 + 6*7^18 + 6*7^19 + O(7^20) + ( 0 )*pi
        sage: print(K(3) * K(5))
        1 + 2*7 + O(7^20) + ( O(7^20) )*pi
        sage: print(K.gen())
        0 + ( 1 + O(7^20) )*pi
        sage: print(K.gen()**2)
        7 + O(7^21) + ( O(7^20) )*pi
        sage: print((K(1) + K.gen())**2)
        1 + 7 + O(7^20) + ( 2 + O(7^20) )*pi
        sage: print(K(3)/K(2))
        5 + 3*7 + 3*7^2 + 3*7^3 + 3*7^4 + 3*7^5 + 3*7^6 + 3*7^7 + 3*7^8 + 3*7^9 + 3*7^10 + 3*7^11 + 3*7^12 + 3*7^13 + 3*7^14 + 3*7^15 + 3*7^16 + 3*7^17 + 3*7^18 + 3*7^19 + O(7^20) + ( 0 )*pi
        sage: print(K(3,2)/K(5,6))
        2 + 5*7 + 4*7^2 + 2*7^4 + 3*7^5 + 4*7^6 + 3*7^7 + 5*7^8 + 7^9 + 4*7^10 + 3*7^11 + 3*7^12 + 4*7^13 + 5*7^14 + 2*7^15 + 5*7^17 + 6*7^18 + 2*7^19 + O(7^20) + ( 5 + 4*7^2 + 3*7^4 + 4*7^5 + 7^6 + 7^7 + 3*7^8 + 3*7^9 + 4*7^11 + 5*7^12 + 5*7^13 + 5*7^14 + 5*7^16 + 3*7^17 + 4*7^18 + O(7^20) )*pi
        sage: print(K0(2) * K.gen())
        0 + ( 2 + O(7^20) )*pi
        sage: print(2 * K.gen())
        0 + ( 2 + O(7^20) )*pi

        sage: x = QQ['x'].gen()
        sage: f = x^2 - 3*x + 1
        sage: print(f(K.gen()))
        1 + 7 + O(7^20) + ( 4 + 6*7 + 6*7^2 + 6*7^3 + 6*7^4 + 6*7^5 + 6*7^6 + 6*7^7 + 6*7^8 + 6*7^9 + 6*7^10 + 6*7^11 + 6*7^12 + 6*7^13 + 6*7^14 + 6*7^15 + 6*7^16 + 6*7^17 + 6*7^18 + 6*7^19 + O(7^20) )*pi
        sage: print(K(K.base_ring()(0)))
        0 + ( 0 )*pi

"""
    Element = QuadExtElement
    def __init__(self, base, polynomial, category = None):
        Field.__init__(self,base, category = category or Fields())
        self._p = base.prime()
        try:
            polynomial = ZZ(polynomial)
            x = QQ['x'].gen()
            assert polynomial % self._p == 0
            self._polynomial = x*x - polynomial
        except TypeError:
            self._polynomial = polynomial
        if not self._polynomial.is_monic():
            raise ValueError("Polynomial must be monic")
        self._prec = base.precision_cap()
        if self._polynomial[1] == 0:
            self._rs = None, self._polynomial[0]
        else:
            self._rs = -self._polynomial[1], self._polynomial[0]

    def precision_cap(self):
        return self._prec

    def characteristic(self):
        return self.base().characteristic()

    def base_ring(self):
        return self.base().base_ring()

    def characteristic(self):
        return self.base().characteristic()

    def gen(self):
        return self.element_class(self, 0, 1)

    def unramified_generator(self):
        return self.element_class(self, self.base().gen())

    def prime(self):
        return self._p

    def polynomial(self):
        return self._polynomial

    def _element_constructor_(self, *args, **kwds):
        if len(args) != 1:
           return self.element_class(self, *args, **kwds)
        x = args[0]
        if isinstance(x,list):
            return self.element_class(self, x[0], x[1], **kwds)
        else:
            return self.element_class(self, x, **kwds)

    # Implement coercion from the base and from fraction fields
    def _coerce_map_from_(self, S):
        if self.base().has_coerce_map_from(S):
            return True

    # return some elements of this parent
    def _an_element_(self):
        a = self.base().an_element()
        b = self.base_ring().an_element()
        return self.element_class(self,a,b)

    def some_elements(self):
        return [self.an_element(),self.element_class(self,self.base().an_element()),self.element_class(self, self.base_ring().an_element())]

    def random_element(self):
        base = self.base()
        return self.element_class(self, (base.random_element(),base.random_element()), check=False)

    def _repr_(self):
        return 'Quadratic extension defined by %s over its base.'%self._polynomial

    def uniformizer(self):
        return self.gen()

    def residue_class_degree(self):
        return self.base().residue_class_degree()

    def ramification_index(self):
        return self.polynomial().degree()

    def relative_degree(self):
        return self.polynomial().degree()

    def absolute_degree(self):
        return self.relative_degree() * self.base().degree()

    def is_finite(self):
        return self.base().is_finite()

