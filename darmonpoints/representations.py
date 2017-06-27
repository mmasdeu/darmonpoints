######################
##                  ##
##  REPRESENTATIONS ##
##                  ##
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
from util import *
import os
from ocmodule import OCVn
from sage.misc.persist import db,db_save
from sage.parallel.decorate import fork,parallel
from sage.matrix.constructor import block_matrix
from sage.rings.number_field.number_field import NumberField
from sage.categories.action import Action
import operator
from cohomology_abstract import *
from sage.matrix.matrix_space import MatrixSpace
from sage.modules.free_module_element import vector
from sage.modules.vector_integer_dense import Vector_integer_dense
from sage.modules.vector_rational_dense import Vector_rational_dense
from sage.modules.free_module_element import FreeModuleElement_generic_dense

class CoIndAction(Action):
    def __init__(self, algebra , V, G, trivial_action = False):
        self._G = G
        self.V = V
        self._trivial_action = trivial_action
        Action.__init__(self,algebra,V,is_left = True,op = operator.mul)

    def _call_(self,g,v):
        # Here v is an element of the coinduced module
        # v = [v_1, ... , v_r], indexed by cosets
        # To know (g*f)(x_i) = f(x_i g), we write
        # x_i g = g' x_j, and then f(x_i g) = g' f(x_j).
        G = self._G
        V = self.V
        try:
            g = g.quaternion_rep
        except AttributeError:
            pass
        action_data = V.get_action_data(set_immutable(g))
        if self._trivial_action:
            return self.V([v._val[ti] for g1, ti in action_data], check = False)
        else:
            return self.V([g1 * v._val[ti] for g1, ti in action_data], check = False)

class CoIndElement(ModuleElement):
    r'''
    Elements in a co-induced module are represented by lists [v_1,\ldots v_r]
    indexed by the cosets of G(p) \ G(1).
    '''
    def __init__(self, parent, data, check = True):
        V = parent.coefficient_module()
        if check:
            if isinstance(data,list):
                if data[0].parent() is V:
                    self._val = [V(o) for o in data]
                else:
                    dim = len(V.gens())
                    self._val = []
                    for i in range(0,dim * len(parent._G.coset_reps()),dim):
                        self._val.append(V(data[i:i+dim]))
            elif isinstance(data, self.__class__):
                self._val = [V(o) for o in data._val]
                if hasattr(self._val[0],'lift'):
                    prec = self._val[0].parent().precision_cap()
                    self._val = [o.lift(M = prec) for o in self._val]
            elif isinstance(data, Vector_integer_dense) or isinstance(data, Vector_rational_dense):
                data = list(data)
                dim = len(V.gens())
                self._val = []
                for i in range(0,dim * len(parent._G.coset_reps()),dim):
                    self._val.append(V(data[i:i+dim]))
            else:
                self._val = [V(data) for o in parent._G.coset_reps()]
            assert len(self._val) == len(parent._G.coset_reps())
        else:
            self._val = data
        ModuleElement.__init__(self,parent)

    def evaluate_at_identity(self):
        return self._val[0]

    def act_and_evaluate_at_identity(self, g):
        try:
            g = g.quaternion_rep
        except AttributeError:
            pass
        g0, idx = self.parent().get_action_data(set_immutable(g), 0)
        if self.parent()._base_trivial_action:
            return self._val[idx]
        else:
            return g0 * self._val[idx]

    def evaluate(self, x):
        return sum([a * b for a, b in zip(self.values(), x.values())])

    def values(self):
        return self._val

    def __getitem__(self, idx):
        return self._val[idx]

    def _repr_(self):
        return 'Element of %s'%self.parent()

    def _add_(self,right):
        return self.__class__(self.parent(),[ a + b for a,b in zip(self._val,right._val)])

    def _sub_(self,right):
        return self.__class__(self.parent(),[ a - b for a,b in zip(self._val,right._val)])

    def _neg_(self):
        return self.__class__(self.parent(),[ -a for a in self._val])

    def __rmul__(self,right):
        return self.__class__(self.parent(),[ ZZ(right) * a for a in self._val])

    def _cmp_(self, right):
        for u, v in zip(self._val, right._val):
            c = u._cmp_(v)
            if c:
                return c
        return 0

    def __nonzero__(self):
        for v in self._val:
            if v != 0:
                return True
        return False

    def _vector_(self, R = None):
        return vector(sum([list(vector(o)) for o in self.values()],[]))

    def __iter__(self):
        return sum([list(o) for o in self.values()],[]).__iter__()

class CoIndModule(Parent):
    r'''
    A co-induced module.

    TESTS::

        sage: from darmonpoints.homology import *
        sage: from darmonpoints.cohomology_abstract import *
        sage: from darmonpoints.sarithgroup import *
        sage: G = BigArithGroup(5,6,1,outfile='/tmp/darmonpoints.tmp') #  optional - magma
    '''
    Element = CoIndElement
    def __init__(self, G, V, trivial_action = False):
        self._G = G
        self._V = V
        Parent.__init__(self)
        self._act = CoIndAction(G.large_group(), self, G, trivial_action = trivial_action)
        quat_act = CoIndAction(G.large_group().B, self, G, trivial_action = trivial_action)
        self._base_trivial_action = trivial_action
        self._unset_coercions_used()
        self.register_action(self._act)
        self.register_action(quat_act)
        self._populate_coercion_lists_()

    def _repr_(self):
        return 'coInd(G,V) where G is %s and V is %s'%(self._G,self._V)

    def coefficient_module(self):
        return self._V

    def trivial_action(self):
        return self._base_trivial_action

    def base_ring(self):
        return self._V.base_ring()

    def base_field(self):
        return self._V.base_field()

    @cached_method
    def acting_matrix(self, g, prec = None):
        dim = len(self.basis())
        ans = Matrix(self._V.base_ring(),dim, 0)
        for v in self.basis():
            gv = g * v
            gvlist = []
            for w in gv._val:
                try:
                    wlist = list(w)
                except TypeError:
                    wlist = list(w._moments)
                if prec is None:
                    gvlist.extend(wlist)
                else:
                    gvlist.extend(wlist[:prec])
            ans = ans.augment(Matrix(self._V.base_ring(),dim,1,gvlist))
        return ans

    def act_by_genpow(self, i, a, v):
        G = self._G
        g = G.large_group().gen(i).quaternion_rep**a
        action_data = self.get_action_data(set_immutable(g))
        if self._base_trivial_action:
            return [v[ti] for g1, ti in action_data]
        else:
            return [g1 * v[ti] for g1, ti in action_data]

    @cached_method
    def get_action_data(self, g, idx = None):
        G = self._G
        if idx is None:
            return [G.get_coset_ti(set_immutable(xi * g)) for xi in G.coset_reps()]
        else:
            return G.get_coset_ti(set_immutable(G.coset_reps()[idx] * g))

    def group(self):
        return self._G

    def _element_constructor_(self, x, check = True):
        return self.element_class(self, x, check)

    @cached_method
    def gens(self):
        try:
            return tuple([self.gen(i) for i in range(len(self._V.gens()) * len(self._G.coset_reps()))])
        except AttributeError:
            return tuple([self.gen(i) for i in range(len(self._V.basis()) * len(self._G.coset_reps()))])

    def basis(self):
        return self.gens()

    def dimension(self):
        return len(self.gens())

    @cached_method
    def gen(self, i):
        V = self._V
        try:
            gens = V.gens()
        except AttributeError:
            gens = V.basis()
        i0 = i / len(gens)
        i1 = i % len(gens)
        ans = [V(0) for g in self._G.coset_reps()]
        ans[i0] = gens[i1]
        return self(ans)

class IndElement(CoIndElement):
    def evaluate_at_identity(self):
        raise NotImplementedError

class IndAction(CoIndAction):
    pass

class IndModule(CoIndModule):
    Element = IndElement
    def __init__(self, G, V, trivial_action = False):
        self._G = G
        self._V = V
        Parent.__init__(self)
        self._act = IndAction(G.large_group(), self, G, trivial_action = trivial_action)
        quat_act = IndAction(G.large_group().B, self, G, trivial_action = trivial_action)
        self._base_trivial_action = trivial_action
        self._unset_coercions_used()
        self.register_action(self._act)
        self.register_action(quat_act)
        self._populate_coercion_lists_()

    def _repr_(self):
        return 'Ind(G,V) where G is %s and V is %s'%(self._G,self._V)

