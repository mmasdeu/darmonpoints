import operator
import os
from collections import defaultdict
from itertools import chain, groupby, islice, product, starmap, tee

from sage.arith.all import GCD
from sage.categories.action import Action
from sage.matrix.all import Matrix, matrix
from sage.matrix.matrix_space import MatrixSpace
from sage.misc.cachefunc import cached_method
from sage.misc.misc_c import prod
from sage.misc.verbose import verbose
from sage.modules.free_module import FreeModule
from sage.modules.free_module_element import free_module_element
from sage.modules.module import Module
from sage.rings.infinity import Infinity
from sage.rings.integer import Integer
from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import Qq, ZpCA
from sage.rings.padics.precision_error import PrecisionError
from sage.rings.power_series_ring import PowerSeriesRing
from sage.sets.set import Set
from sage.structure.element import ModuleElement, MultiplicativeGroupElement
from sage.structure.parent import Parent
from sage.structure.richcmp import richcmp
from sage.structure.sage_object import SageObject
from sage.structure.unique_representation import (
    CachedRepresentation,
    UniqueRepresentation,
)


# Returns a hash of an element of Cp (which is a quadratic extension of Qp)
def _hash(x):
    try:
        return hash(x)
    except TypeError:
        pass
    try:
        return hash(str(x))
    except TypeError:
        pass
    try:
        ans = [x.valuation()]
    except (AttributeError, TypeError):
        return hash(x)
    for tup in x.list()[:100]:
        ans.extend(tup)
    return tuple(ans)


class DivisorsElement(ModuleElement):
    def __init__(self, parent, data, ptdata=None):
        r"""
        A Divisor is given by a list of pairs (P,nP), where P is a point, and nP is an integer.

        TESTS::

            sage: from darmonpoints.divisors import Divisors
            sage: Cp.<g> = Qq(5^3,20)
            sage: Div = Divisors(Cp)
            sage: D1 = Div(g+3)
            sage: D2 = Div(2*g+1)
            sage: D = D1 + D2
            sage: print(-D)
            Divisor of degree -2
            sage: print(2*D1 + 5*D2)
            Divisor of degree 7
        """
        self._data = defaultdict(ZZ)
        self._ptdict = {}
        ModuleElement.__init__(self, parent)
        if data == 0 and (
            not hasattr(data, "parent") or data.parent() != parent.base()
        ):
            return
        if isinstance(data, DivisorsElement):
            self._data.update(data._data)
            self._ptdict.update(data._ptdict)
        elif isinstance(data, list):
            for n, P in data:
                if n == 0:
                    continue
                hP = _hash(P)
                self._data[hP] += n
                self._ptdict[hP] = P
                if self._data[hP] == 0:
                    del self._data[hP]
                    del self._ptdict[hP]
        elif isinstance(data, dict):
            assert ptdata is not None
            self._data.update(data)
            self._ptdict.update(ptdata)
        else:
            if data != Infinity:
                P = self.parent().base()(data)
            else:
                P = data
            hP = _hash(P)
            self._data[hP] = 1
            self._ptdict[hP] = P

    def apply_map(self, f):
        return self.parent()([(n, f(self._ptdict[hP])) for hP, n in self._data.items()])

    def restrict(self, condition):
        return self.parent()(
            [
                (n, self._ptdict[hP])
                for hP, n in self._data.items()
                if condition(self._ptdict[hP])
            ]
        )

    def __iter__(self):
        return iter(((self._ptdict[hP], n) for hP, n in self._data.items()))

    def _repr_(self):
        return "Divisor of degree %s" % self.degree()

    def _cache_key(self):
        return tuple([self.parent(), tuple([(hP, n) for hP, n in self._data.items()])])

    def value(self):
        if len(self._data) == 0:
            return "0"
        is_first = True
        mystr = ""
        for hP, n in self._data.items():
            if not is_first:
                mystr += " + "
            else:
                is_first = False
            mystr += "%s*(%s)" % (n, self._ptdict[hP])
        return mystr

    def __eq__(self, right):
        return self._data == self.parent()(right)._data

    def is_zero(self):
        return all(n == 0 for n in self._data.values())

    def gcd(self):
        return GCD([n for n in self._data.values()])

    def _add_(self, right):
        newdict = defaultdict(ZZ)
        newdict.update(self._data)
        new_ptdata = {}
        new_ptdata.update(self._ptdict)
        new_ptdata.update(right._ptdict)
        for hP, n in right._data.items():
            newdict[hP] += n
            if newdict[hP] == 0:
                del newdict[hP]
                del new_ptdata[hP]
            else:
                new_ptdata[hP] = right._ptdict[hP]
        return self.__class__(self.parent(), newdict, ptdata=new_ptdata)

    def _sub_(self, right):
        newdict = defaultdict(ZZ)
        newdict.update(self._data)
        new_ptdata = {}
        new_ptdata.update(self._ptdict)
        new_ptdata.update(right._ptdict)
        for hP, n in right._data.items():
            newdict[hP] -= n
            if newdict[hP] == 0:
                del newdict[hP]
                del new_ptdata[hP]
            else:
                new_ptdata[hP] = right._ptdict[hP]
        return self.__class__(self.parent(), newdict, ptdata=new_ptdata)

    def _neg_(self):
        newdict = defaultdict(ZZ)
        new_ptdata = {}
        new_ptdata.update(self._ptdict)
        for P, n in self._data.items():
            newdict[P] = -n
        return self.__class__(self.parent(), newdict, ptdata=new_ptdata)

    def scale_by(self, a):
        if a == 0:
            return self.__class__(self.parent(), {}, ptdata={})

        newdict = defaultdict(ZZ)
        new_ptdata = {}
        new_ptdata.update(self._ptdict)
        for P, n in self._data.items():
            newdict[P] = a * n
        return self.__class__(self.parent(), newdict, ptdata=new_ptdata)

    def _acted_upon_(self, g, on_left):
        assert not on_left
        if isinstance(g, Integer) or isinstance(g, int):
            return self.scale_by(g)
        else:
            assert hasattr(g, "nrows")
            return self.left_act_by_matrix(g)

    def left_act_by_matrix(self, g):
        a, b, c, d = g.list()
        gp = self.parent()
        K = self.parent().base_ring()
        newdict = defaultdict(ZZ)
        new_ptdata = {}
        for P, n in self:
            if P == Infinity:
                try:
                    new_pt = K(a) / K(c)
                except ZeroDivisionError:
                    new_pt = Infinity
            else:
                new_pt = (K(a) * P + K(b)) / (K(c) * P + K(d))
            hnew_pt = _hash(new_pt)
            newdict[hnew_pt] += n
            new_ptdata[hnew_pt] = new_pt
            if newdict[hnew_pt] == 0:
                del newdict[hnew_pt]
                del new_ptdata[hnew_pt]
            else:
                new_ptdata[hnew_pt] = new_pt
        return gp(newdict, ptdata=new_ptdata)

    @cached_method
    def degree(self):
        return sum(self._data.values())

    @cached_method
    def size(self):
        r"""
        Returns the size of self, defined as the sum of the absolute
        values of the coefficients.
        """
        return sum(ZZ(d).abs() for d in self._data.values())

    def support(self):
        return [self._ptdict[P] for P in Set([d for d in self._data])]

    def __getitem__(self, P):
        return self._ptdict[P]

    def __setitem__(self, P, val):
        self._ptdict[P] = val

    def pair_with(self, D):
        rat = self.rational_function(as_map=True)
        return prod((rat(P) ** n for P, n in D), self.parent().base_ring()(1)).log(0)

    def rational_function(self, as_map=False, z=None):
        if as_map:
            return lambda z: prod(((1 - z / P) ** n for P, n in self), z.parent()(1))
        else:
            if z is None:
                z = PolynomialRing(self.parent()._field, names="z").gen()
            return prod(((1 - z / P) ** n for P, n in self), z.parent()(1))

    def as_list_of_differences(self):
        if self.degree() != 0:
            raise ValueError("The degree of the divisor should be zero")
        ans = []
        newdata = {P: n for P, n in self._data.items()}
        while len(newdata) > 0:
            P = next(P for P, n in newdata.items() if n > 0)
            Q = next(Q for Q, n in newdata.items() if n < 0)
            newdata[P] -= 1
            if newdata[P] == 0:
                del newdata[P]
            newdata[Q] += 1
            if newdata[Q] == 0:
                del newdata[Q]
            ans.append((self._ptdict[P], self._ptdict[Q]))
        return ans


class Divisors(Parent, CachedRepresentation):
    Element = DivisorsElement

    def __init__(self, base):
        self._base = base
        Parent.__init__(self)

    def _an_element_(self):
        return self.element_class(self, [(3, self._base._an_element_())])

    def _element_constructor_(self, data, ptdata=None):
        return self.element_class(self, data, ptdata)

    def _coerce_map_from_(self, S):
        if isinstance(S, self.__class__):
            return S._base is self._base
        else:
            return False

    def base(self):
        return self._base

    def _repr_(self):
        return "Group of divisors over " + repr(self._base)
