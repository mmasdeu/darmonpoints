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
from sage.matrix.constructor import column_matrix
from sage.misc.lazy_attribute import lazy_attribute
from sage.matrix.matrix_space import MatrixSpace

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
        if isinstance(data,list):
            self._val = [V(o) for o in data]
        else:
            self._val = [V(data.evaluate(b)) for b in parent.group().gens()]
        if parent.trivial_action():
            self.evaluate = self.evaluate_trivial
        else:
            self.evaluate = self.evaluate_general
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

    def evaluate_trivial(self,x,parallelize = False):
        G = self.parent().group()
        try:
            word = tuple(x.word_rep)
        except AttributeError:
            word = tuple(G(x).word_rep)
        V = self.parent().coefficient_module()
        Gab = G.abelianization()
        ans = V(0)
        cvals = [V(o) for o in self._val]
        weight_vector = [0 for g in G.gens()]
        for i,a in word:
            weight_vector[i] += a
        for g, a in zip(G.gens(),weight_vector):
            if a == 0:
                continue
            ans += a * sum([ZZ(a0) * b for a0,b in zip(list(Gab.G_to_ab_free(g)),cvals)], V(0))
        return ans

    @cached_method
    def evaluate_general(self,x,parallelize = False):
        H = self.parent()
        G = H.group()
        if hasattr(x,'word_rep'):
            wd  = x.word_rep
        else:
            x = G(x)
            wd = x.word_rep
        if len(wd) == 0:
            return H.coefficient_module()(0)
        if True: #H._use_ps_dists:
            if len(wd) == 1:
                return self._evaluate_syllable(*wd[0])
            else:
                return self._evaluate_word(wd)
        i,a = wd[-1]
        ans = H.eval_at_genpow(i,a,self).reduce_mod()
        for i, a in reversed(wd[:-1]):
            ans = H.eval_at_genpow(i,a,self) + H.mul_by_gen_pow(i,a,ans)
        return ans

    def _evaluate_syllable(self,g,a):
        G = self.parent().group()
        V = self.parent().coefficient_module()
        if a == 1:
            return self._val[g]
        elif a == 0:
            return V(0)
        elif a == -1:
            return -(G.gen(g)**-1 * self._val[g])

        elif a < 0:
            phig = self._val[g]
            tmp = V(phig)
            for i in xrange(-a-1):
                tmp = phig + G.gen(g) * tmp
            return -(G.gen(g)**a * tmp)

        else:
            phig = self._val[g]
            tmp = V(phig)
            for i in xrange(a-1):
                tmp = phig + G.gen(g) * tmp
            return tmp

    def _evaluate_word(self,word):
        r''' Evaluate recursively, using cocycle condition:
        self(gh) = self(g) + g*self(h)
        This implies also that:
        1) self(g^a) = self(g^b) + g^b*self(g^(a-b)) (will apply it to b = a // 2, a > 0
        2) self(g^-1) = - g^(-1)*self(g)
        '''
        G = self.parent().group()
        V = self.parent().coefficient_module()
        lenword = len(word)
        if lenword > 1:
            pivot = ZZ(lenword) // ZZ(2)
            word_prefix = word[:pivot]
            gamma = prod([G.gen(g)**a for g,a in word_prefix],G.one())
            return self._evaluate_word(tuple(word_prefix)) + gamma * self._evaluate_word(tuple(word[pivot:]))

        if lenword == 0:
            return V(0)

        if lenword == 1:
            return self._evaluate_syllable(*word[0])

class CohomologyGroup(Parent):
    def __init__(self, G, V, trivial_action = False):
        self._group = G
        self._coeffmodule = V
        self._trivial_action = trivial_action
        self._gen_pows = []
        self._gen_pows_neg = []
        if trivial_action:
            self._acting_matrix = lambda x, y: matrix(V.base_ring(),V.dimension(),V.dimension(),1)
        else:
            self._acting_matrix = lambda x, y: V.acting_matrix(x, y)
        onemat = G(1)
        try:
            dim = V.dimension()
        except AttributeError:
            dim = len(V.basis())
        one = Matrix(V.base_ring(),dim,dim,1)
        for i,g in enumerate(G.gens()):
            try:
                A = self._acting_matrix(g, dim)
            except AttributeError: # DEBUG
                gmat = G.embed(G.Ugens[i], dim)
                gmat.set_immutable()
                A = self._acting_matrix(gmat, dim)
            self._gen_pows.append([one, A])
            try:
                Ainv = self._acting_matrix(g**-1, dim)
            except AttributeError: # DEBUG
                gmatinv = gmat.adjoint() # gmat**-1
                gmatinv.set_immutable()
                Ainv = self._acting_matrix(gmatinv, dim)
            self._gen_pows_neg.append([one, Ainv])
        Parent.__init__(self)
        return

    def trivial_action(self):
        return self._trivial_action

    def group(self):
        return self._group

    def coefficient_module(self):
        return self._coeffmodule

    @lazy_attribute
    def space(self):
        r'''
        Calculates the space of cocyles modulo coboundaries, as a Z-module.

        TESTS::

        sage: from sarithgroup import *
        sage: from cohomology_abstract import *
        sage: from ocmodule import *
        sage: GS = BigArithGroup(5, 6, 1)
        sage: G = GS.small_group()
        sage: V = OCVn(5,1)
        sage: Coh = CohomologyGroup(G,V,trivial_action = False)
        sage: amb = Coh.space
        '''
        V = self.coefficient_module()
        R = V.base_ring()
        Vdim = V.dimension()
        G = self.group()
        if self.trivial_action():
            return R**(Vdim * len(self.group().abelianization().free_gens()))
        else:
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
            return cocycles.quotient(coboundaries)

    @cached_method
    def dimension(self):
        try:
            return len([o for o in self.space.invariants() if o == 0])
        except AttributeError:
            return self.space.rank()

    def zero(self):
        if self.trivial_action():
            return self.element_class(self,[self._coeffmodule(0) for g in xrange(len(self.group().abelianization().free_gens()))])
        else:
            return self.element_class(self,[self._coeffmodule(0) for g in xrange(self.gens())])

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
        vi = self.space.basis()[i]
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
        h = self.get_gen_pow(0,0, red)
        ans = [h.new_matrix() for o in self.group().gens()]
        if len(word) == 0:
            return ans
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

    def mul_by_gen_pow(self,i,a,v):
        ans = v
        V = v.parent()
        if a == 0:
            return ans
        elif a > 0:
            g = self._gen_pows[i][1]
        else:
            g = self._gen_pows_neg[i][1]
            a = -a
        for o in xrange(a):
            ans = V(g * ans._val).reduce_mod()
        return ans

