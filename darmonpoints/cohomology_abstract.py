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
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,LaurentSeriesRing, Qp,Zp,Zmod, Infinity
from sage.arith.all import gcd, lcm
from collections import defaultdict
from itertools import product,chain,izip,groupby,islice,tee,starmap
from util import *
import os
from ocmodule import OCVn
from sage.misc.persist import db,db_save
from sage.parallel.decorate import fork,parallel
oo = Infinity
from sage.matrix.constructor import block_matrix
from sage.rings.number_field.number_field import NumberField
from sage.categories.action import Action
import operator
from sage.matrix.constructor import column_matrix
from sage.misc.lazy_attribute import lazy_attribute
from sage.matrix.matrix_space import MatrixSpace

from sage.rings.padics.precision_error import PrecisionError
from sage.modules.free_module_element import free_module_element, vector

class CohomologyElement(ModuleElement):
    def __init__(self, parent, data):
        r'''
        Define an element of `H^1(G,V)`

        INPUT:
            - G: a BigArithGroup
            - V: a CoeffModule
            - data: a list

        TESTS::

            sage: from darmonpoints.sarithgroup import BigArithGroup
            sage: from darmonpoints.cohomology_arithmetic import ArithCoh
            sage: G = BigArithGroup(5,6,1,use_shapiro=False,outfile='/tmp/darmonpoints.tmp') #  optional - magma
            sage: Coh = ArithCoh(G) #  optional - magma
            sage: 2 in Coh.hecke_matrix(13).eigenvalues() #  optional - magma
            True
            sage: -4 in Coh.hecke_matrix(7).eigenvalues() #  optional - magma
            True
            sage: PhiE = Coh.gen(1) #  optional - magma
        '''
        G = parent.group()
        V = parent.coefficient_module()
        if isinstance(data,list):
            self._val = [V(o) for o in data]
        else:
            self._val = [V(data.evaluate(b)) for b in parent.group().gens()]
        ModuleElement.__init__(self,parent)

    def values(self):
        return self._val

    def _vector_(self, R = None):
        ambient = self.parent().space()
        ans = vector(sum([list(o) for o in self._val], []))
        return ambient(ambient.V()(ans))

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

    def is_zero(self):
        for u in self.values():
            if not u.is_zero():
                return False
        return True

    def valuation(self, p = None):
        return min([ u.valuation(p) for u in self._val ])

    def pair_with_cycle(self, xi):
        if self.parent().trivial_action():
            return sum([a * self.evaluate(g) for a, g in zip(xi.values(), self.parent().group().gens())])
        else:
            return sum([self.evaluate(g).evaluate(a) for a, g in zip(xi.values(), self.parent().group().gens())])

    @cached_method
    def evaluate_and_identity(self,x,parallelize = False):
        H = self.parent()
        G = H.group()
        if x.parent() is G:
            wd  = x.word_rep
        else:
            x = G(x)
            wd = x.word_rep
        if self.parent().trivial_action():
            return self._evaluate_word_tietze_trivial_identity(wd)
        else:
            return self._evaluate_word_tietze_identity(wd)

    @cached_method
    def evaluate(self,x,parallelize = False):
        H = self.parent()
        G = H.group()
        if x.parent() is G:
            wd  = x.word_rep
        else:
            x = G(x)
            wd = x.word_rep
        if self.parent().trivial_action():
            return self._evaluate_word_tietze_trivial(wd)
        else:
            return self._evaluate_word_tietze(wd)

    def _evaluate_word_tietze(self,word):
        G = self.parent().group()
        V = self.parent().coefficient_module()

        if len(word) == 0:
            return V(0)
        g = word[0]
        if g > 0:
            ans = self._val[g-1]
            gamma = G.gen(g-1)
        else:
            g0 = -g-1
            gamma = G.gen(g0)**-1
            ans = -(gamma * self._val[g0])
        for g in word[1:]:
            if g > 0:
                ans += gamma * self._val[g-1]
                gamma = gamma * G.gen(g-1)
            else:
                g0 = -g-1
                gamma = gamma * G.gen(g0)**-1
                ans -= gamma * self._val[g0]
        return ans

    def _evaluate_word_tietze_identity(self,word):
        G = self.parent().group()
        V = self.parent().coefficient_module()

        if len(word) == 0:
            return V(0)[0]
        g = word[0]
        if g > 0:
            ans = self._val[g-1][0]
            gamma = G.gen(g-1)
        else:
            g0 = -g-1
            gamma = G.gen(g0)**-1
            ans = - self._val[g0].act_and_evaluate_at_identity(gamma)
        for g in word[1:]:
            if g > 0:
                ans += self._val[g-1].act_and_evaluate_at_identity(gamma)
                gamma = gamma * G.gen(g-1)
            else:
                g0 = -g-1
                gamma = gamma * G.gen(g0)**-1
                ans -= self._val[g0].act_and_evaluate_at_identity(gamma)
        return ans

    def _evaluate_word_tietze_trivial(self,word):
        G = self.parent().group()
        V = self.parent().coefficient_module()
        ans = V(0)
        for g in word:
            if g > 0:
                ans += self._val[g-1]
            else:
                ans -= self._val[-g-1]
        return ans

    def _evaluate_word_tietze_trivial_identity(self,word):
        G = self.parent().group()
        V = self.parent().coefficient_module()
        ans = V(0)[0]
        for g in word:
            if g > 0:
                ans += self._val[g-1][0]
            else:
                ans -= self._val[-g-1][0]
        return ans

class CohomologyGroup(Parent):
    def __init__(self, G, V, trivial_action = False):
        self._group = G
        self._coeffmodule = V
        self._trivial_action = trivial_action
        self._gen_pows = []
        self._gen_pows_neg = []
        if trivial_action:
            self._acting_matrix = lambda x, y: matrix(V.base_ring(),V.dimension(),V.dimension(),1)
            gens_local = [ (None, None) for g in G.gens() ]
        else:
            def acting_matrix(x,y):
                try:
                    return V.acting_matrix(x,y)
                except AttributeError:
                    return V.acting_matrix(G.embed(x.quaternion_rep,V.base_ring().precision_cap()), y)
            self._acting_matrix = acting_matrix
            gens_local = [ (g, g**-1) for g in G.gens() ]
        onemat = G(1)
        try:
            dim = V.dimension()
        except AttributeError:
            dim = len(V.basis())
        one = Matrix(V.base_ring(),dim,dim,1)
        for g, ginv in gens_local:
            A = self._acting_matrix(g, dim)
            self._gen_pows.append([one, A])
            Ainv = self._acting_matrix(ginv, dim)
            self._gen_pows_neg.append([one, Ainv])
        Parent.__init__(self)
        return

    def trivial_action(self):
        return self._trivial_action

    def group(self):
        return self._group

    def coefficient_module(self):
        return self._coeffmodule

    @cached_method
    def space(self):
        r'''
        Calculates the space of cocyles modulo coboundaries, as a Z-module.

        TESTS:

        sage: from darmonpoints.sarithgroup import *
        sage: from darmonpoints.cohomology_abstract import *
        sage: from darmonpoints.ocmodule import *
        sage: GS = BigArithGroup(5, 6,1,use_shapiro=False,outfile='/tmp/darmonpoints.tmp') #  optional - magma
        sage: G = GS.large_group() #  optional - magma
        sage: V = OCVn(5,1)     #  optional - magma
        sage: Coh = CohomologyGroup(G,V,trivial_action = False) #  optional - magma
        '''
        verb = get_verbose()
        set_verbose(0)
        V = self.coefficient_module()
        R = V.base_ring()
        Vdim = V.dimension()
        G = self.group()
        gens = G.gens()
        ambient = R**(Vdim * len(gens))
        # Now find the subspace of cocycles
        A = Matrix(R, Vdim * len(gens), 0)
        for r in G.get_relation_words():
            Alist = self.fox_gradient(r)
            newA = block_matrix(Alist, nrows = 1)
            A = A.augment(newA.transpose())
        A = A.transpose()
        cocycles = ambient.submodule([ambient(o) for o in A.right_kernel_matrix().rows()])
        gmat = block_matrix([self._gen_pows[i][1] - 1 for i in range(len(G.gens()))], nrows = len(G.gens()))
        coboundaries = cocycles.submodule([ambient(o) for o in gmat.columns()])
        ans = cocycles.quotient(coboundaries)
        set_verbose(verb)
        return ans

    @cached_method
    def dimension(self):
        try:
            return len([o for o in self.space().invariants() if o == 0])
        except AttributeError:
            return self.space().rank()

    def zero(self):
        return self.element_class(self,[self._coeffmodule(0) for g in xrange(len(self.group().gens()))])

    def _an_element_(self):
        return self.zero()

    def _element_constructor_(self, x):
        return self.element_class(self, x)

    def _coerce_map_from_(self,S):
        if isinstance(S,CohomologyGroup):
            return True
        else:
            return False

    @cached_method
    def gen(self,i):
        vi = self.space().gen(i)
        try:
            vi = vi.lift()
        except AttributeError: pass
        vi = list(vi)
        V = self.coefficient_module()
        Vdim = V.dimension()
        data = []
        for i in range(0,len(vi),Vdim):
            data.append(V(vi[i:i+Vdim]))
        return CohomologyElement(self, data)

    def gens(self):
        return [self.gen(i) for i in xrange(self.dimension())]

    def _repr_(self):
        return 'H^1(G,V), with G being %s and V = %s'%(self.group(),self.coefficient_module())

    def fox_gradient(self, word, red = None):
        if red is None:
            red = lambda x:x
        V = self.coefficient_module()
        h = self.get_gen_pow(0,0, red)
        ans = [self._gen_pows[0][0].parent()(0) for o in self.group().gens()]
        if len(word) == 0:
            return ans
        word = tietze_to_syllables(word)
        lenword = len(word)
        for j in xrange(lenword):
            i,a = word[j]
            ans[i] += h  * self.get_fox_term(i,a, red)
            ans[i] = red(ans[i])
            if j < lenword -1:
                h = red(h * self.get_gen_pow(i,a, red))
        return ans

    def get_gen_pow(self,i,a, red = None):
        if red is None:
            red = lambda x:x
        if a == 0:
            return self._gen_pows[0][0]
        elif a > 0:
            genpows = self._gen_pows[i]
        else:
            genpows = self._gen_pows_neg[i]
            a = -a
        while len(genpows) <= a:
            tmp = genpows[1] * genpows[-1]
            genpows.append(red(tmp))
        return genpows[a]

    def get_fox_term(self,i,a, red = None):
        if red is None:
            red = lambda x:x
        if a == 1:
            return self._gen_pows[i][0]
        elif a == -1:
            return -self._gen_pows_neg[i][1]
        elif a > 1:
            genpows = self._gen_pows[i]
            ans = genpows[0] + genpows[1]
            for o in xrange(a-2):
                ans = red(ans)
                ans = genpows[0] + genpows[1] * ans
            return red(ans)
        elif a < -1:
            a = -a
            genpows = self._gen_pows_neg[i]
            ans = genpows[0] + genpows[1]
            for o in xrange(a-2):
                ans = red(ans)
                ans = genpows[0] + genpows[1] * ans
            ans = -genpows[1] * ans
            return red(ans)


    def eval_at_genpow(self,i,a,v, red = None):
        if red is None:
            red = lambda x:x
        V = v._val[i].parent()
        v = v._val[i]._val
        if a == 1:
            return V(v)
        elif a == -1:
            return V(-(self._gen_pows_neg[i][1] * v))
        elif a > 1:
            genpows = self._gen_pows[i]
            ans = V(v + genpows[1] * v)
            for o in xrange(a-2):
                ans.reduce_mod()
                ans = V(v) + V(genpows[1] * ans._val)
            return ans.reduce_mod()
        elif a < -1:
            a = -a
            genpows = self._gen_pows_neg[i]
            ans = V(v) + V(genpows[1] * v)
            for o in xrange(a-2):
                ans.reduce_mod()
                ans = V(v) + V(genpows[1] * ans._val)
            ans = V(-genpows[1] * ans._val)
            return ans.reduce_mod()
