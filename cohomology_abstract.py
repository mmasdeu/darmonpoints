######################
##                  ##
##    COHOMOLOGY    ##
##                  ##
######################
from sage.structure.sage_object import SageObject
from sage.groups.group import AlgebraicGroup
from sage.structure.element import MultiplicativeGroupElement,ModuleElement
from sage.structure.parent import Parent
from sage.categories.homset import Hom
from sage.matrix.constructor import Matrix,matrix
from sage.misc.cachefunc import cached_method
from sage.structure.sage_object import load,save
from sage.misc.misc_c import prod
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,LaurentSeriesRing,lcm, Qp,Zp,Zmod
from collections import defaultdict
from itertools import product,chain,izip,groupby,islice,tee,starmap
from sigma0 import Sigma0,Sigma0ActionAdjuster
from sage.rings.infinity import Infinity
from sage.rings.arith import GCD
from util import *
import os
from ocmodule import OCVn
from sage.misc.persist import db,db_save
from sage.schemes.plane_curves.constructor import Curve
from sage.parallel.decorate import fork,parallel
oo = Infinity
from sage.matrix.constructor import block_matrix
from sage.rings.number_field.number_field import NumberField
from sage.categories.action import Action
import operator


class CohomologyElement(ModuleElement):
    def __init__(self, parent, data):
        r'''
        Define an element of `H^1(G,V)`

        INPUT:
            - G: a BigArithGroup
            - V: a CoeffModule
            - data: a list

        TESTS:
            sage: G = BigArithGroup(5,6,1)
            sage: V = QQ^1
            sage: Coh = Cohomology(G,V)
            sage: print Coh.hecke_matrix(13).eigenvalues()
            [2,2]
            sage: print Coh.hecke_matrix(7).eigenvalues()
            [4,-4]
            sage: PhiE = Coh.gen(1)
        '''
        G = parent.group()
        V = parent.coefficient_module()
        # self._val = [V(data.evaluate(b)) for b in parent.group().gens()]
        if isinstance(data,list):
            self._val = [V(0) if o.is_zero() else V(o) for o in data]
        else:
            self._val = [V(data.evaluate(b)) for b in parent.group().gens()]
        if parent.is_overconvergent:
            self.evaluate = self.evaluate_oc
        else:
            self.evaluate = self.evaluate_triv
        ModuleElement.__init__(self,parent)

    def values(self):
        return self._val

    def _repr_(self):
        return 'Cohomology class in %s'%self.parent()

    def _add_(self,right):
        return self.__class__(self.parent(), [ a + b for a,b in zip(self._val,right._val) ])

    def _sub_(self,right):
        return self.__class__(self.parent(), [ a - b for a,b in zip(self._val,right._val) ])

    def _neg_(self):
        return self.__class__(self.parent(), [ -a for a in self._val ])

    def __rmul__(self,right):
        return self.__class__(self.parent(), [ ZZ(right) * a for a in self._val ])

    def valuation(self, p = None):
        return min([ u.valuation(p) for u in self._val ])

class CohomologyGroup(Parent):
    def __init__(self):
        return

    def group(self):
        return self._group

    def coefficient_module(self):
        return self._coeffmodule

    def dimension(self): # Warning
        return self._num_abgens * self._coeffmodule.dimension()

    def zero(self):
        return self.element_class(self,[self._coeffmodule(0) for g in xrange(self._num_abgens)])

    def _an_element_(self):
        return self.zero()

    def _coerce_map_from_(self,S):
        if isinstance(S,CohomologyGroup):
            return True
        else:
            return False

    def _element_constructor_(self,data):
        if isinstance(data,list):
            return self.element_class(self, data)
        else:
            assert isinstance(data,self.element_class)
            G = self.group()
            V = self.coefficient_module()
            if data.parent().is_overconvergent:
                try:
                    return self.element_class(self,[V(data.get_liftee().evaluate(g).moment(0)) for g in G.gens()])
                except RuntimeError:
                    return self.element_class(self,[V(data.evaluate(g).moment(0).rational_reconstruction()) for g in G.gens()])
            else:
                return self.element_class(self,[V(data.evaluate(g)) for g in G.gens()])

    def fox_gradient(self,word):
        h = self.get_gen_pow(0,0)
        ans = [h.new_matrix() for o in self.group().gens()]
        if len(word) == 0:
            return ans
        lenword = len(word)
        for j in xrange(lenword):
            i,a = word[j]
            ans[i] += h  * self.get_fox_term(i,a)
            ans[i] = ans[i].apply_map(lambda x: x % self._pN)
            if j < lenword -1:
                h = h * self.get_gen_pow(i,a)
                h = h.apply_map(lambda x: x % self._pN)
        return ans

    def get_gen_pow(self,i,a):
        if a == 0:
            return self._gen_pows[0][0]
        elif a > 0:
            genpows = self._gen_pows[i]
        else:
            genpows = self._gen_pows_neg[i]
            a = -a
        while len(genpows) <= a:
            tmp = genpows[1] * genpows[-1]
            genpows.append(tmp.apply_map(lambda x:x % self._pN))
        return genpows[a]

    def get_fox_term(self,i,a):
        if a == 1:
            return self._gen_pows[i][0]
        elif a == -1:
            return -self._gen_pows_neg[i][1]
        elif a > 1:
            genpows = self._gen_pows[i]
            ans = genpows[0] + genpows[1]
            for o in xrange(a-2):
                ans = ans.apply_map(lambda x: x % self._pN)
                ans = genpows[0] + genpows[1] * ans
            ans = ans.apply_map(lambda x: x % self._pN)
            return ans
        elif a < -1:
            a = -a
            genpows = self._gen_pows_neg[i]
            ans = genpows[0] + genpows[1]
            for o in xrange(a-2):
                ans = ans.apply_map(lambda x: x % self._pN)
                ans = genpows[0] + genpows[1] * ans
            ans = -genpows[1] * ans
            ans = ans.apply_map(lambda x: x % self._pN)
            return ans

    def eval_at_genpow(self,i,a,v):
        v = v[i]._val
        if a == 1:
            return v
        elif a == -1:
            return -(self._gen_pows_neg[i][1] * v)
        elif a > 1:
            genpows = self._gen_pows[i]
            ans = v + genpows[1] * v
            for o in xrange(a-2):
                ans = ans.apply_map(lambda x: x % self._pN)
                ans = v + genpows[1] * ans
            ans = ans.apply_map(lambda x: x % self._pN)
            return ans
        elif a < -1:
            a = -a
            genpows = self._gen_pows_neg[i]
            ans = v + genpows[1] * v
            for o in xrange(a-2):
                ans = ans.apply_map(lambda x: x % self._pN)
                ans = v + genpows[1] * ans
            ans = -genpows[1] * ans
            ans = ans.apply_map(lambda x: x % self._pN)
            return ans

    def mul_by_gen_pow(self,i,a,v):
        ans = v
        if a == 0:
            return ans
        elif a > 0:
            g = self._gen_pows[i][1]
        else:
            g = self._gen_pows_neg[i][1]
            a = -a
        for o in xrange(a):
            ans = (g * ans).apply_map(lambda x: x % self._pN)
        return ans
