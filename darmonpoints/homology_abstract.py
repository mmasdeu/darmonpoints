######################
##                  ##
##    ABSTRACT      ##
##     HOMOLOGY     ##
##                  ##
######################
from sage.structure.sage_object import SageObject
from sage.misc.cachefunc import cached_method
from collections import defaultdict
from sage.matrix.all import matrix,Matrix
from itertools import product,chain,izip,groupby,islice,tee,starmap
#from distributions import Distributions, Symk
from sage.structure.parent import Parent
from sage.categories.action import Action
from sage.rings.padics.factory import Qq
from sage.sets.set import Set
from sage.modules.free_module_element import vector
from util import *
import os
import operator
from sage.rings.arith import GCD
from representations import *

class HomologyElement(ModuleElement):
    def __init__(self, parent, data):
        r'''
        Define an element of `H_1(G,V)`

        INPUT:
            - G: a BigArithGroup
            - V: a CoeffModule
            - data: a list

        '''
        G = parent.group()
        V = parent.coefficient_module()
        if isinstance(data,list):
            self._val = [V(o) for o in data]
        ModuleElement.__init__(self,parent)

    def values(self):
        return self._val

    def _vector_(self, R = None):
        ambient = self.parent().space()
        ans = vector(sum([list(o) for o in self._val], []))
        V = ambient
        try:
            V = V.V()
        except AttributeError:
            pass
        return ambient(V(ans))

    def _repr_(self):
        return 'Homology class in %s'%self.parent()

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

class HomologyGroup(Parent):
    Element = HomologyElement
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
                except:
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
        Calculates the homology space as a Z-module.
        '''
        verb = get_verbose()
        set_verbose(0)
        V = self.coefficient_module()
        R = V.base_ring()
        Vdim = V.dimension()
        G = self.group()
        gens = G.gens()
        ambient = R**(Vdim * len(gens))
        if self.trivial_action():
            cycles = ambient
        else:
            # Now find the subspace of cycles
            A = Matrix(R, Vdim, 0)
            for g in gens:
                for v in V.gens():
                    A = A.augment(matrix(R,Vdim,1,list(vector(g**-1 * v - v))))
            K = A.right_kernel_matrix()
            cycles = ambient.submodule([ambient(list(o)) for o in K.rows()])
        boundaries = []
        for r in G.get_relation_words():
            grad = self.twisted_fox_gradient(G(r).word_rep)
            for v in V.gens():
                boundaries.append(cycles(ambient(sum([list(a * vector(v)) for a in grad],[]))))
        boundaries = cycles.submodule(boundaries)
        ans = cycles.quotient(boundaries)
        set_verbose(verb)
        return ans

    @cached_method
    def rank(self):
        try:
            return len([o for o in self.space().invariants() if o == 0])
        except AttributeError:
            return self.space().rank()

    def zero(self):
        if self.trivial_action():
            if self.coefficient_module().dimension() > 1:
                raise NotImplementedError
            else:
                return self.element_class(self,[self._coeffmodule(0) for g in xrange(len(self.group().abelianization()))])
        else:
            return self.element_class(self,[self._coeffmodule(0) for g in xrange(len(self.group().gens()))])

    def _an_element_(self):
        return self.zero()

    def _element_constructor_(self, x):
        if x == 0:
            V = self.coefficient_module()
            return self.element_class(self, [V(0) for o in self.group().gens()])
        elif isinstance(x, list):
            return self.element_class(self, x)
        elif isinstance(x, tuple) and len(x) == 2:
            G = self.group()
            V = self.coefficient_module()
            g, v = x
            v = V(v)
            grad = self.twisted_fox_gradient(G(g).word_rep)
            return self.element_class(self, [V(a * vector(v)) for a in grad])
        else:
            vi = self.space()(x)
            try:
                vi = self.space().lift(vi)
            except AttributeError: pass
            try:
                vi = vi.lift()
            except AttributeError: pass
            vi = list(vi)
            V = self.coefficient_module()
            Vdim = V.dimension()
            data = []
            for i in range(0,len(vi),Vdim):
                data.append(V(vi[i:i+Vdim]))
            return self.element_class(self, data)

    def _coerce_map_from_(self,S):
        if isinstance(S,HomologyGroup):
            return True
        else:
            return False

    @cached_method
    def gen(self,i):
        vi = self.space().gen(i)
        try:
            vi = self.space().lift(vi)
        except AttributeError: pass
        try:
            vi = vi.lift()
        except AttributeError: pass
        vi = list(vi)
        V = self.coefficient_module()
        Vdim = V.dimension()
        data = []
        for i in range(0,len(vi),Vdim):
            data.append(V(vi[i:i+Vdim]))
        return self.element_class(self, data)

    @cached_method
    def free_gens(self):
        ans = []
        for i, g in enumerate(self.space().gens()):
            try:
                good = self.space().invariants()[i] == 0
            except AttributeError:
                good = True
            if good:
                ans.append(self.gen(i))
        return ans

    def gens(self):
        return [self.gen(i) for i in xrange(self.ngens())]

    def ngens(self):
        return self.space().ngens()

    def _repr_(self):
        return 'H_1(G,V), with G being %s and V = %s'%(self.group(),self.coefficient_module())

    def twisted_fox_gradient(self, word, red = None):
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
            ans[i] += self.get_twisted_fox_term(i,a, red) * h
            ans[i] = red(ans[i])
            if j < lenword -1:
                h = red(self.get_gen_pow(i, -a, red) * h)
            ans[i] = ans[i].change_ring(ZZ)
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

    def get_twisted_fox_term(self,i,a, red = None):
        verb_level = get_verbose()
        set_verbose(0)
        if red is None:
            red = lambda x:x
        if a == 1:
            ans = self._gen_pows[i][0]
        elif a == -1:
            ans = -self._gen_pows_neg[i][1]**-1
        elif a > 1:
            genpows = self._gen_pows[i]
            ans = genpows[0] + genpows[1]**-1
            for o in xrange(a-2):
                ans = red(ans)
                ans = genpows[0] + genpows[1]**-1 * ans
            ans = red(ans)
        elif a < -1:
            a = -a
            genpows = self._gen_pows_neg[i]
            ans = genpows[0] + genpows[1]**-1
            for o in xrange(a-2):
                ans = red(ans)
                ans = genpows[0] + genpows[1]**-1 * ans
            ans = -genpows[1]**-1 * ans
            ans = red(ans)
        set_verbose(verb_level)
        return ans

class ArithHomologyElement(HomologyElement):
    def _repr_(self):
        return 'Arithmetic homology class in %s'%self.parent()

class ArithHomology(HomologyGroup):
    Element = ArithHomologyElement
    def __init__(self, G, V, trivial_action = True):
        self._use_shapiro = G._use_shapiro
        if self._use_shapiro:
            group = G.large_group()
            W = IndModule(G,V, trivial_action = trivial_action)
            HomologyGroup.__init__(self, group, W, trivial_action = False)
        else:
            group = G.small_group()
            W = V
            HomologyGroup.__init__(self, group, W, trivial_action = trivial_action)

    @cached_method
    def hecke_matrix(self, l, use_magma = True, g0 = None, with_torsion = False): # l can be oo
        verb = get_verbose()
        set_verbose(0)
        if with_torsion:
            dim = len(self.gens())
            gens = self.gens()
        else:
            dim = self.rank()
            gens = self.free_gens()
        R = self.coefficient_module().base_ring()
        M = matrix(R,dim,dim,0)
        coeff_dim = self.coefficient_module().dimension()

        for j,cycle in enumerate(gens):
            # Construct column j of the matrix
            new_col = vector(self.apply_hecke_operator(cycle, l, use_magma = use_magma, g0 = g0))
            if with_torsion:
                M.set_column(j,list(new_col))
            else:
                try:
                    invs = self.space().invariants()
                    M.set_column(j,[o for o,a in zip(new_col,invs) if a == 0])
                except AttributeError:
                    M.set_column(j,list(new_col))
        set_verbose(verb)
        return M

    def apply_hecke_operator(self,c,l, hecke_reps = None,group = None,scale = 1,use_magma = True,g0 = None):
        r"""
        Apply the l-th Hecke operator operator to ``c``.
        """
        # verbose('Entering apply_hecke_operator')
        if hecke_reps is None:
            hecke_reps = self.group().get_hecke_reps(l,use_magma = use_magma) # Assume l != p here!
        # verbose('Got hecke reps')
        V = self.coefficient_module()
        padic = not V.base_ring().is_exact()
        group = self.group()
        if padic:
            prec = V.base_ring().precision_cap()
        else:
            prec = None
        vals = []
        R = V.base_ring()
        gammas = group.gens()
        ans = self([V(0) for gamma in gammas])
        # verbose('Calculating action')
        for gamma, v in zip(gammas, c.values()):
            for g in hecke_reps:
                if self.trivial_action():
                    ans += self((group.get_hecke_ti(g,gamma,l,use_magma),v))
                else:
                    ans += self((group.get_hecke_ti(g,gamma,l,use_magma),g.conjugate() * v))
        return scale * ans

class ArithHomologyElement(HomologyElement):
    pass
