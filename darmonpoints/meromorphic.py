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
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.structure.unique_representation import UniqueRepresentation
from sage.rings.rational_field import QQ
from sage.rings.integer_ring import ZZ
from sage.rings.padics.padic_generic import pAdicGeneric
from sage.categories.pushout import pushout
from sage.rings.infinity import Infinity
from sage.structure.richcmp import richcmp
from sage.structure.sage_object import load,save
from sage.structure.unique_representation import CachedRepresentation
from sage.structure.parent import Parent
from sage.modules.vector_integer_dense import Vector_integer_dense
from sage.modules.free_module_element import FreeModuleElement_generic_dense
from sage.misc.cachefunc import cached_method
from sage.misc.all import cputime
from sage.misc.verbose import verbose, get_verbose, set_verbose
from sage.misc.misc_c import prod
from sage.misc.cachefunc import cached_function
from sage.modules.free_module_element import free_module_element as vector
from sage.rings.padics.precision_error import PrecisionError
from copy import deepcopy
from .divisors import Divisors

class MeromorphicFunctionsElement(ModuleElement):
    def __init__(self, parent, data, check=True):
        # verbose(f'{check = }')
        ModuleElement.__init__(self,parent)
        if check:
            K = parent.base_ring()
            prec = parent._prec
            Ps = parent._Ps
            if isinstance(data.parent(), Divisors):
                phi = self.parent()._divisors_to_pseries
                self._value = Ps(1)
                for Q, n in data:
                    self._value *= phi(K(Q))**n
                self._value /= self._value[0]
                if len(data.support()) == 1:
                    self.normalize_point = Q + 1 # DEBUG
            elif data == 0:
                self._value = Ps(1) # multiplicative!
            elif data.parent() == parent:
                self._value = deepcopy(data._value)
            else:
                val = Ps(data)
                val /= val[0]
                self._value = val.add_bigoh(prec)
        else:
            self._value = deepcopy(data)
        self._moments = self._value

    def power_series(self):
        return self.parent().power_series_ring()(self._value)

    def __call__(self, D):
        return self.evaluate(D)

    def evaluate(self, D): # meromorphic functions
        K = self.parent().base_ring()
        phi = self.parent()._eval_pseries_map
        poly = self._value.polynomial()
        a, b, c, d = self.parent()._parameter.list()
        try:
            pt = phi(self.normalize_point)
            pole = -d / c
            valinf = poly(pt) * (self.normalize_point - pole)
        except AttributeError:
            pt = a / c
            pole = None
            valinf = poly(pt)
        if isinstance(D.parent(), Divisors):
            return prod((poly(phi(P))/valinf * ((P - pole) if pole is not None else 1) )**n for P, n in D)
        else:
            return (poly(phi(D)) / valinf * ((D - pole) if pole is not None else 1))

    def _cmp_(self, right):
        return (self._value > right._value) - (self._value < right._value)

    def __nonzero__(self):
        return self._value != 1

    def valuation(self, p=None):
        K = self.parent().base_ring()
        return min([Infinity] + [o.valuation(p) for o in (self._value-1).coefficients()])

    def _add_(self, right): # multiplicative!
        ans = self._value * right._value
        return self.__class__(self.parent(), ans, check=False)

    def _sub_(self, right): # multiplicative!
        ans = self._value / right._value
        return self.__class__(self.parent(), ans, check=False)

    def _neg_(self): # multiplicative!
        ans = self._value**-1
        return self.__class__(self.parent(), ans, check=False)

    def _repr_(self):
        return repr(self._value)

    def scale_by(self, k): # multiplicative!
        ans = self._value**k
        return self.__class__(self.parent(), ans, check=False)

    def _acted_upon_(self, g, on_left):
        assert not on_left
        if isinstance(g, Integer):
            return self.scale_by(g)
        else:
            return self.left_act_by_matrix(g)

    def left_act_by_matrix(self, g, param=None): # meromorphic functions
        Ps = self._value.parent()
        K = self.parent().base_ring()
        prec = self.parent()._prec
        p = self.parent()._p
        # Below we code the action which is compatible with the usual action
        # P |-> (aP+b)/(cP+D)
        radius = tuple((ky, val) for ky, val in self.parent().radius.items())
        zz_ps_vec, new_param = self.parent().get_action_data(g, param=param)
        if param is None:
            param = new_param
        poly = self._value.polynomial()
        ans = sum(a * zz_ps_vec[e] for a, e in zip(poly.coefficients(), poly.exponents()))
        ans /= ans[0] # always normalize
        ans = ans.add_bigoh(prec)
        return MeromorphicFunctions(K, param, p=p, prec=prec, radius=radius)(ans)

class MeromorphicFunctions(Parent, UniqueRepresentation):
    r'''
    TESTS:

    '''
    Element = MeromorphicFunctionsElement

    @staticmethod
    def __classcall__(cls, K, parameter, **kwargs):
        p = kwargs.pop('p', None)
        prec = kwargs.pop('prec', None)
        radius = kwargs.pop('radius', None)
        try:
            parameter = parameter.change_ring(QQ)
        except AttributeError: pass
        parameter.set_immutable()
        return super().__classcall__(cls, K, parameter, radius, p, prec)

    def __init__(self, K, parameter, radius, p, prec):
        Parent.__init__(self)
        if prec is None:
            self._prec = K.precision_cap()
        else:
            self._prec = prec

        self._p = p
        self._prec = prec
        self.radius = dict(radius)
        self._base_ring = K
        psprec = self._prec
        self._Ps = PowerSeriesRing(self._base_ring, names='t', default_prec=psprec)

        self._parameter = Matrix(K,2,2,parameter)
        a, b, c, d = self._parameter.list()
        self._eval_pseries_map = lambda Q : (Q.parent()(a) * Q + Q.parent()(b)) / (Q.parent()(c) * Q + Q.parent()(d))
        # Maps Q to 1 - t / ((a*Q+b)/(c*Q+d))
        self._divisors_to_pseries = lambda Q : 1 - (Q.parent()(c) * Q + Q.parent()(d)) * self._Ps.gen() / (Q.parent()(a) * Q + Q.parent()(b))
        # Maps Q to t - Q
        # self._divisors_to_pseries = lambda Q : self._Ps.gen() - (a * Q + b)/(c*Q+d)


    def prime(self):
        return self._p

    def parameter(self):
        return self._parameter

    @cached_method
    def get_action_data(self, g, K = None, prec = None, param=None):
        verb_level = get_verbose()
        set_verbose(0)
        g.set_immutable()
        if prec is None:
            prec = self._prec
        if K is None:
            K = self.base_ring()
        if param is None:
            try:
                r = self.radius[g]
            except (TypeError, KeyError):
                r = 1 # DEBUG
                print('WARNING: could not find radius...')
            tg = find_parameter(g,r).change_ring(K)
        else:
            tg = param.change_ring(K)
        a, b, c, d = (self._parameter * (tg * g).adjugate()).list()
        zz = (self._Ps([b,a]) / self._Ps([d,c])).truncate(prec)
        Ps = self._Ps
        ans = [Ps(1), zz]
        for _ in range(prec - 1):
            zz_ps = (zz * ans[-1]).truncate(prec+1)
            ans.append(zz_ps)
        set_verbose(verb_level)
        return ans, tg

    def base_ring(self):
        return self._base_ring

    def power_series_ring(self):
        return self._Ps

    def _element_constructor_(self, data, check=True):
        return self.element_class(self, data, check=check)

    def _repr_(self):
        return "Meromorphic Multiplicative Functions over %s with parameter %s, p = %s and prec = %s"%(self._base_ring, self._parameter, self._p, self._prec)

class RationalFunctionsElement(ModuleElement):
    def __init__(self, parent, data, check=True):
        if check:
            K = parent.base_ring()
            FF = parent._V
            z = FF.gen()
            if data == 0:
                self._value = FF(1)
            elif isinstance(data.parent(), Divisors):
                self._value = FF(1)
                for Q, n in data:
                    self._value *= (1 - z / K(Q))**n
            elif data.parent() == FF:
                self._value = FF(data)
        else:
            self._value = data
        ModuleElement.__init__(self,parent)

    def numerator(self):
        return self._value.numerator()

    def denominator(self):
        return self._value.denominator()

    def power_series(self, names = None):
        if names is None:
            names = 't'
        K = self.parent().base_ring()
        try:
            prec = K.precision_cap()
        except AttributeError:
            prec = 20 # DEBUG
        Ps = PowerSeriesRing(K,names,default_prec=prec)
        ans = Ps(self._value)
        return ans

    def rational_function(self):
        return self._value

    def __call__(self, D):
        return self.evaluate(D)

    def evaluate(self, D):
        if isinstance(D.parent(), Divisors):
            return prod(self._value(P)**ZZ(n) for P, n in D)
        else:
            return self._value(D)

    def _cmp_(self, right):
        return (self._value > right._value) - (self._value < right._value)

    def __nonzero__(self):
        return self._value != 1

    def _add_(self, right):
        ans = self._value * right._value
        return self.__class__(self.parent(), ans, check=False)

    def _sub_(self, right):
        ans = self._value / right._value
        return self.__class__(self.parent(), ans, check=False)

    def _neg_(self):
        ans = self._value**-1
        return self.__class__(self.parent(), ans, check=False)

    def _repr_(self):
        return repr(self._value)

    def scale_by(self, k):
        ans = self._value**k
        return self.__class__(self.parent(), ans, check=False)

    def _acted_upon_(self, g, on_left):
        assert not on_left
        if isinstance(g, Integer):
            return self.scale_by(g)
        else:
            return self.left_act_by_matrix(g)

    def left_act_by_matrix(self, g): # rational functions
        Ps = self._value.parent()
        K = Ps.base_ring()
        # Below we code the action which is compatible with the usual action
        # P |-> (aP+b)/(cP+D)
        z = self._value.parent().gen()
        a, b, c, d = g.list()
        num, den = self._value.numerator(), self._value.denominator()
        assert num.degree() == den.degree()
        deg = num.degree()
        new_num = sum(ai * (d*z-b)**i * (-c*z+a)**(deg-i) for ai, i in zip(num.coefficients(), num.exponents()))
        new_num /= new_num(0)
        new_den = sum(ai * (d*z-b)**i * (-c*z+a)**(deg-i) for ai, i in zip(den.coefficients(), den.exponents()))
        new_den /= new_den(0)
        try:
            ans = new_num / new_den
        except ZeroDivisionError:
            print(f'{den = }')
            print(f'{a = }, {b = }, {c = }, {d = }')
            print(new_den)
            assert 0
        return self.__class__(self.parent(),ans,check=False)

class RationalFunctions(Parent, CachedRepresentation):
    r'''

    '''
    Element = RationalFunctionsElement
    def __init__(self, K):
        Parent.__init__(self)
        self._base_ring = K
        self._V = PolynomialRing(K, names = 'z')

    def base_ring(self):
        return self._base_ring

    def _element_constructor_(self, data):
        return self.element_class(self, data)

    def _repr_(self):
        return "Field of Rational Functions over %s"%(self._base_ring)
