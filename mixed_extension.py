from sage.rings.padics.padic_generic import pAdicGeneric
from sage.structure.element import Element
from sage.modules.free_module_element import FreeModuleElement_generic_dense, vector
from sage.categories.fields import Fields
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.element import FieldElement
from sage.rings.ring import Field
from sage.rings.integer_ring import Z as ZZ
from sage.rings.all import QQ

class QuadExtElement(FieldElement):
    def __init__(self, parent, x, y = None, check = True):
        self._p = parent._p
        if parent is None:
            raise ValueError("The parent must be provided")
        if not check:
            self._value = x
        else:
            B = parent.base()
            if y is None:
                y = B.zero()
            if x not in B or y not in B:
                raise ValueError("Both arguments must be elements of %s"%B)
            x = B(x)
            y = B(y)
            self._value = vector(B, 2, [x, y])
        FieldElement.__init__(self, parent)

    # Needed for the class
    def _repr_(self):
        return '%s + ( %s )*pi'%(self._value[0], self._value[1])

    def __nonzero__(self):
        return self._value.__nonzero__()

    def list(self):
        return self._value.list()

    # Arithmetic
    def _add_(self, right):
        return self.__class__(self.parent(), self._value + right._value, check = False)

    def _sub_(self, right):
        return self.__class__(self.parent(), self._value - right._value, check = False)

    def _mul_(self, right):
        a, b = self._value.list()
        c, d = right._value.list()
        r, s = self.parent()._rs
        bd = b*d
        base = self.parent().base()
        return self.__class__(self.parent(),vector(base,2,[a*c - bd*s, a*d+b*c-bd*r]), check = False)

    def _div_(self, right):
        a, b = self._value
        c, d = right._value
        r, s = self.parent()._rs
        den = c*c - c*d*r + d*d*s
        base = self.parent().base()
        return self.__class__(self.parent(), vector(base,2,[(a*c-a*d*r+b*d*s) / den, (b*c-a*d) / den]), check = False)

    def _cmp_(self, right):
        return cmp(self._value,right._value)
    __cmp__ = _cmp_

    def valuation(self, p = None):
        a, b = self._value
        return min([2 * a.valuation(p), b.valuation(p) + 1])

    def ordp(self, p = None):
        a, b = self._value
        return self.valuation(p)/2

    def trace_relative(self):
        a, b = self._value
        base = self.parent().base()
        r, _ = self.parent()._rs
        return base(a) - base(b) * base(r)

    def trace_absolute(self):
        y = self.trace_relative()
        if hasattr(y,'trace'):
            return y.trace()
        else:
            return y.trace_absolute()

class QuadExt(UniqueRepresentation, Field): # Implement extension by x^2 + r*x + s
    r"""
    A quadratic extension of a p-adic field.

    EXAMPLES::

        sage: from mixed_extension import *
        sage: p = 7
        sage: K0.<z> = Qq(p**2,20)
        sage: K = QuadExt(K0, p)
        sage: print K(3) + K(5)
        1 + 7 + O(7^20) + ( 0 )*pi
        sage: print K(3) - K(5)
        5 + 6*7 + 6*7^2 + 6*7^3 + 6*7^4 + 6*7^5 + 6*7^6 + 6*7^7 + 6*7^8 + 6*7^9 + 6*7^10 + 6*7^11 + 6*7^12 + 6*7^13 + 6*7^14 + 6*7^15 + 6*7^16 + 6*7^17 + 6*7^18 + 6*7^19 + O(7^20) + ( 0 )*pi
        sage: print K(3) * K(5)
        1 + 2*7 + O(7^20) + ( 0 )*pi
        sage: print K.gen()
        0 + ( 1 + O(7^20) )*pi
        sage: print K.gen()**2
        7 + O(7^21) + ( 0 )*pi
        sage: print (K(1) + K.gen())**2
        1 + 7 + O(7^20) + ( 2 + O(7^20) )*pi
        sage: print K(3)/K(2)
        5 + 3*7 + 3*7^2 + 3*7^3 + 3*7^4 + 3*7^5 + 3*7^6 + 3*7^7 + 3*7^8 + 3*7^9 + 3*7^10 + 3*7^11 + 3*7^12 + 3*7^13 + 3*7^14 + 3*7^15 + 3*7^16 + 3*7^17 + 3*7^18 + 3*7^19 + O(7^20) + ( 0 )*pi
        sage: print K(3,2)/K(5,6)
        2 + 5*7 + 4*7^2 + 2*7^4 + 3*7^5 + 4*7^6 + 3*7^7 + 5*7^8 + 7^9 + 4*7^10 + 3*7^11 + 3*7^12 + 4*7^13 + 5*7^14 + 2*7^15 + 5*7^17 + 6*7^18 + 2*7^19 + O(7^20) + ( 5 + 4*7^2 + 3*7^4 + 4*7^5 + 7^6 + 7^7 + 3*7^8 + 3*7^9 + 4*7^11 + 5*7^12 + 5*7^13 + 5*7^14 + 5*7^16 + 3*7^17 + 4*7^18 + O(7^20) )*pi
        sage: print K0(2) * K.gen()
        0 + ( 2 + O(7^20) )*pi
        sage: print 2 * K.gen()
        0 + ( 2 + O(7^20) )*pi

        sage: x = QQ['x'].gen()
        sage: f = x^2 - 3*x + 1
        sage: print f(K.gen())
        1 + 7 + O(7^20) + ( 4 + 6*7 + 6*7^2 + 6*7^3 + 6*7^4 + 6*7^5 + 6*7^6 + 6*7^7 + 6*7^8 + 6*7^9 + 6*7^10 + 6*7^11 + 6*7^12 + 6*7^13 + 6*7^14 + 6*7^15 + 6*7^16 + 6*7^17 + 6*7^18 + 6*7^19 + O(7^20) )*pi
        sage: print K(K.base_ring()(0))
        0 + ( 0 )*pi

"""
    Element = QuadExtElement
    def __init__(self, base, polynomial, category = None):
        Field.__init__(self,base, category = category or Fields())
        self._p = base.prime()
        try:
            polynomial = ZZ(polynomial)
            x = QQ['x'].gen()
            self._polynomial = x*x - self._p
        except TypeError:
            self._polynomial = polynomial
        if not self._polynomial.is_monic():
            raise ValueError("Polynomial must be monic")
        self._prec = base.precision_cap()
        self._rs = self._polynomial[1], self._polynomial[0]


    def precision_cap(self):
        return self._prec

    def characteristic(self):
        return self.base().characteristic()

    def base_ring(self):
        return self.base().base_ring()

    def characteristic(self):
        return self.base().characteristic()

    def gen(self):
        return self.element_class(self, self.base()(0), self.base()(1))

    def unramified_generator(self):
        return self.element_class(self, self.base().gen())

    def prime(self):
        return self._p

    def polynomial(self):
        return self._polynomial

    def _element_constructor_(self, *args, **kwds):
        if len(args)!=1:
           return self.element_class(self, *args, **kwds)
        x = args[0]
        try:
            P = x.parent()
        except AttributeError:
            return self.element_class(self, x, **kwds)
        if isinstance(x,list) or isinstance(P,FreeModuleElement_generic_dense):
            return self.element_class(self, x[0],x[1], **kwds)
        else:
            return self.element_class(self, x, *kwds)

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

    def _repr_(self):
        return 'Quadratic extension of %s by %s'%(self._base, self._polynomial)

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
