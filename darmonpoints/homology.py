######################
##                  ##
##     HOMOLOGY     ##
##                  ##
######################
from sage.structure.sage_object import SageObject
from sage.misc.cachefunc import cached_method
from sage.matrix.all import matrix,Matrix
from sage.structure.richcmp import richcmp
from sage.structure.parent import Parent
from sage.categories.action import Action
from sage.rings.padics.factory import Qq
from sage.rings.integer_ring import ZZ
from sage.rings.power_series_ring import PowerSeriesRing
from sage.sets.set import Set
from sage.arith.all import GCD
from sage.rings.padics.precision_error import PrecisionError
from sage.structure.element import MultiplicativeGroupElement,ModuleElement
from sage.modules.module import Module
from sage.matrix.matrix_space import MatrixSpace
from sage.modules.free_module import FreeModule
from sage.modules.free_module_element import  free_module_element
from sage.structure.unique_representation import CachedRepresentation
from sage.rings.padics.factory import ZpCA
from sage.structure.richcmp import richcmp
from sage.structure.unique_representation import UniqueRepresentation

import os
import operator

from itertools import product,chain,groupby,islice,tee,starmap
from collections import defaultdict

from .homology_abstract import ArithHomology, HomologyGroup
from .representations import *
from .util import *

def lattice_homology_cycle(p, G, wp, xlist, prec, tau = None, outfile = None, smoothen = None):
    if tau is None:
        Cp = Qq(p**2,prec,names = 'g')
        wpinv_mat = (G.embed(wp,prec)**-1).change_ring(Cp)
        a,b,c,d = wpinv_mat.list()
        tau = (a*Cp.gen() + b)/(c*Cp.gen() + d)
    else:
        Cp = tau.parent()
        wpinv_mat = (G.embed(wp,prec)**-1).change_ring(Cp)
    Div = Divisors(Cp)
    H1 = OneChains(G,Div)
    xi1 = H1(0)
    xi2 = H1(0)
    for x, a in xlist:
        xi1 += H1({G(x.quaternion_rep) : Div(tau)}).mult_by(a)
        xi2 += H1({G(wp**-1 * x.quaternion_rep * wp) :  wpinv_mat * Div(tau)}).mult_by(a)
    xi10 = xi1
    xi20 = xi2
    while True:
        try:
            newxi1 = xi1.zero_degree_equivalent()
            newxi2 = xi2.zero_degree_equivalent()
            break
        except ValueError:
            xi1 = xi1 + xi10
            xi2 = xi2 + xi20
    if smoothen is not None:
        newxi1 = newxi1.hecke_smoothen(smoothen)
        newxi2 = newxi2.hecke_smoothen(smoothen)
    return newxi1, newxi2


# Returns a hash of an element of Cp (which is a quadratic extension of Qp)
def _hash(x):
    try:
        return hash(x)
    except TypeError: pass
    try:
        return hash(str(x))
    except TypeError: pass
    try:
        ans = [x.valuation()]
    except (AttributeError,TypeError):
        return hash(x)
    for tup in x.list()[:100]:
        ans.extend(tup)
    return tuple(ans)

class DivisorsElement(ModuleElement):
    def __init__(self,parent,data,ptdata = None):
        r'''
        A Divisor is given by a list of pairs (P,nP), where P is a point, and nP is an integer.

        TESTS:

            sage: from darmonpoints.homology import Divisors
            sage: Cp.<g> = Qq(5^3,20)
            sage: Div = Divisors(Cp)
            sage: D1 = Div(g+3)
            sage: D2 = Div(2*g+1)
            sage: D = D1 + D2
            sage: print(-D)
            Divisor of degree -2
            sage: print(2*D1 + 5*D2)
            Divisor of degree 7
        '''
        self._data = defaultdict(ZZ)
        self._ptdict = {}
        ModuleElement.__init__(self,parent)
        if data == 0:
            return
        elif isinstance(data,DivisorsElement):
            self._data.update(data._data)
            self._ptdict.update(data._ptdict)
        elif isinstance(data,list):
            for n,P in data:
                if n == 0:
                    continue
                hP = _hash(P)
                self._data[hP] += n
                self._ptdict[hP] = P
                if self._data[hP] == 0:
                    del self._data[hP]
                    del self._ptdict[hP]
        elif isinstance(data,dict):
            assert ptdata is not None
            self._data.update(data)
            self._ptdict.update(ptdata)
        else:
            if data != Infinity:
                P = self.parent().base_field()(data)
            else:
                P = data
            hP = _hash(P)
            self._data[hP] = 1
            self._ptdict[hP] = P

    def apply_map(self, f):
        return self.parent()([(n, f(self._ptdict[hP])) for hP, n in self._data.items()])

    def restrict(self, condition):
        return self.parent()([(n, self._ptdict[hP]) for hP, n in self._data.items() if condition(self._ptdict[hP])])

    def __iter__(self):
        return iter(((self._ptdict[hP],n) for hP,n in self._data.items()))

    def _repr_(self):
        return 'Divisor of degree %s'%self.degree()

    def _cache_key(self):
        return tuple([self.parent(),tuple([(hP, n) for hP, n in self._data.items()])])

    def value(self):
        if len(self._data) == 0:
            return '0'
        is_first = True
        mystr = ''
        for hP,n in self._data.items():
            if not is_first:
                mystr += ' + '
            else:
                is_first = False
            mystr += '%s*(%s)'%(n,self._ptdict[hP])
        return mystr

    def __eq__(self, right):
        return self._data == self.parent()(right)._data

    def is_zero(self):
        return all((n == 0 for n in self._data.values()))

    def gcd(self):
        return GCD([n for n in self._data.values()])

    def _add_(self,right):
        newdict = defaultdict(ZZ)
        newdict.update(self._data)
        new_ptdata = {}
        new_ptdata.update(self._ptdict)
        new_ptdata.update(right._ptdict)
        for hP,n in right._data.items():
            newdict[hP] += n
            if newdict[hP] == 0:
                del newdict[hP]
                del new_ptdata[hP]
            else:
                new_ptdata[hP] = right._ptdict[hP]
        return self.__class__(self.parent(),newdict,ptdata = new_ptdata)

    def radius(self):
        ans = 0
        for P,n in self:
            ans = max(ans,point_radius(P))
        return ans

    def _sub_(self,right):
        newdict = defaultdict(ZZ)
        newdict.update(self._data)
        new_ptdata = {}
        new_ptdata.update(self._ptdict)
        new_ptdata.update(right._ptdict)
        for hP,n in right._data.items():
            newdict[hP] -= n
            if newdict[hP] == 0:
                del newdict[hP]
                del new_ptdata[hP]
            else:
                new_ptdata[hP] = right._ptdict[hP]
        return self.__class__(self.parent(),newdict,ptdata = new_ptdata)

    def _neg_(self):
        newdict = defaultdict(ZZ)
        new_ptdata = {}
        new_ptdata.update(self._ptdict)
        for P,n in self._data.items():
            newdict[P] = -n
        return self.__class__(self.parent(),newdict,ptdata = new_ptdata)

    def scale_by(self, a):
        if a == 0:
            return self.__class__(self.parent(), {}, ptdata={})

        newdict = defaultdict(ZZ)
        new_ptdata = {}
        new_ptdata.update(self._ptdict)
        for P,n in self._data.items():
            newdict[P] = a * n
        return self.__class__(self.parent(),newdict,ptdata = new_ptdata)

    def left_act_by_matrix(self,g): # divisors
        a,b,c,d = g.list()
        gp = self.parent()
        K = self.parent().base_ring()
        newdict = defaultdict(ZZ)
        new_ptdata = {}
        for P,n in self:
            if P == Infinity:
                try:
                    new_pt = K(a)/K(c)
                except ZeroDivisionError:
                    new_pt = Infinity
            else:
                new_pt = (K(a)*P+K(b))/(K(c)*P+K(d))
            hnew_pt = _hash(new_pt)
            newdict[hnew_pt] += n
            new_ptdata[hnew_pt] = new_pt
            if newdict[hnew_pt] == 0:
                del newdict[hnew_pt]
                del new_ptdata[hnew_pt]
            else:
                new_ptdata[hnew_pt] = new_pt
        return gp(newdict,ptdata = new_ptdata)

    @cached_method
    def degree(self):
        return sum(self._data.values())

    @cached_method
    def size(self):
        return sum(ZZ(d).abs() for d in self._data.values())

    def support(self):
        return [self._ptdict[P] for P in Set([d for d in self._data])]

    def __getitem__(self, P):
        return self._ptdict[P]

    def __setitem__(self, P, val):
        self._ptdict[P] = val

    def pair_with(self, D):
        rat = self.rational_function(as_map = True)
        return prod((rat(P)**n for P, n in D), self.parent().base_ring()(1)).log(0)

    def rational_function(self, as_map = False):
        if as_map:
            return lambda z: prod(((1 - z/P)**n for P, n in self), z.parent()(1))
        else:
            z = PolynomialRing(self.parent()._field, names='z').gen()
            return prod(((1 - z/P)**n for P, n in self), z.parent()(1))

class Divisors(Parent, CachedRepresentation):
    Element = DivisorsElement

    def __init__(self,field):
        self._field = field
        Parent.__init__(self)
        self._unset_coercions_used()
        self.register_action(Scaling(ZZ,self))
        self.register_action(MatrixAction(MatrixSpace(self._field,2,2),self))

    def _an_element_(self):
        return self.element_class(self,[(3,self._field._an_element_())])

    def _element_constructor_(self,data,ptdata = None):
        return self.element_class(self,data,ptdata)

    def _coerce_map_from_(self,S):
        if isinstance(S,self.__class__):
            return S._field is self._field
        else:
            return False

    def base_field(self):
        return self._field

    def base_ring(self):
        return self._field

    def _repr_(self):
        return 'Group of divisors over ' + self._field._repr_()

class ArithGroupAction(Action):
    def __init__(self,G,M):
        Action.__init__(self,G,M,is_left = True,op = operator.mul)

    def _act_(self,g,v):
        try:
            K = v.parent().base_ring()
            prec = K.precision_cap()
        except AttributeError:
            prec = -1
        G = g.parent()
        return v.left_act_by_matrix(G.embed(g.quaternion_rep, prec))

class TensorElement(ModuleElement):
    def __init__(self, parent, data):
        r'''
        Define an element of `H_1(G,V)`
            - data: a list

        TESTS:

        '''
        if not isinstance(data,dict):
            raise ValueError('data should be a dictionary indexed by elements of ArithGroup')
        self._data = data
        ModuleElement.__init__(self,parent)

    def __iter__(self):
        return iter(self._data.items())

    def _cache_key(self):
        return tuple([self.parent(), tuple([(g, v._cache_key()) for g, v in self._data.items()])])

    def size_of_support(self):
        return len(self._data)

    def _repr_(self):
        if len(self._data) == 0:
            return '0'
        is_first = True
        mystr = ''
        for g,v in self._data.items():
            if not is_first:
                mystr += ' + '
            else:
                is_first = False
            mystr += '{%s}|(%s)'%(str(g),v)
        return mystr

    def short_rep(self):
        return [(g.size(),v.degree(),v.size()) for g,v in self._data.items()]

    def _add_(self,right):
        newdict = dict()
        for g,v in chain(self._data.items(),right._data.items()):
            try:
                newdict[g] += v
                if newdict[g].is_zero():
                    del newdict[g]
            except KeyError:
                newdict[g] = v
        return self.parent()(newdict)

    def _sub_(self,right):
        newdict = dict(self._data)
        for g,v in right._data.items():
            try:
                newdict[g] -= v
                if newdict[g].is_zero():
                    del newdict[g]
            except KeyError:
                newdict[g] = -v
        return self.parent(newdict)

    def mult_by(self,a):
        return self.__rmul__(a)

    def __rmul__(self,a):
        newdict = {g: a * v for g,v in self._data.items()} if a != 0 else {}
        return self.parent()(newdict)

class TensorProduct(Module, UniqueRepresentation):
    Element = TensorElement
    def __init__(self,G,V):
        r'''
        INPUT:
        - G: an ArithGroup
        - V: a CoeffModule
        '''
        self._group = G
        self._coeffmodule = V
        Module.__init__(self, base=ZZ)
        V._unset_coercions_used()
        V.register_action(ArithGroupAction(G,V))
        self._populate_coercion_lists_()

    def _an_element_(self):
        return self.element_class(self,dict([(self.group().gen(0),self._coeffmodule._an_element_())]))

    def _repr_(self):
        return 'Tensor product of the group ring of %s with %s'%(self.group(), self.coefficient_module())

    def group(self):
        return self._group

    def coefficient_module(self):
        return self._coeffmodule

    def _element_constructor_(self,data):
        if data == 0:
            return self.element_class(self, {})
        if isinstance(data,dict):
            return self.element_class(self,data)
        elif isinstance(data, tuple):
            assert len(tuple) == 2
            return self.element_class(self, {data[0] : data[1]})
        elif isinstance(data, list):
            return self.element_class(self, dict(data))
        else:
            return self.element_class(self, {data : ZZ(1)})

    def _coerce_map_from_(self,S):
        if isinstance(S,self.__class__):
            return S.group() is self.group() and S.coefficient_module() is self.coefficient_module()
        else:
            return False

class OneChainsElement(TensorElement):
    def is_degree_zero_valued(self):
        for v in self._data.values():
            if v.degree() != 0:
                return False
        return True

    def is_zero(self):
        return len(self._data) == 0

    def _nonzero_(self):
        return not self.is_zero()

    def __eq__(self, other):
        return (self - other).is_zero()

    def radius(self):
        return max([0] + [v.radius() for g,v in self._data.items()])

    def zero_degree_equivalent(self, allow_multiple = False, prec=None):
        r'''
        Use the relations:
            * gh|v = g|v + h|g^-1 v
            * g^a|v = g|(v + g^-1v + ... + g^-(a-1)v)
            * g^(-a)|v = - g^a|g^av
        '''
        verbose('Entering zero_degree_equivalent')
        HH = self.parent()
        V = HH.coefficient_module()
        G = HH.group()
        oldvals = list(self._data.values())
        aux_element = list(oldvals[0])[0][0]
        Gab = G.abelianization()
        xlist = [(g,v.degree()) for g,v in zip(self._data.keys(),oldvals)]
        sum_abxlist = sum([Gab((x,n)) for x,n in xlist])
        x_ord = sum_abxlist.order()
        if x_ord == Infinity or (x_ord > 1 and not allow_multiple):
            raise ValueError('Must yield torsion element in abelianization (%s, order = %s)'%(sum_abxlist, x_ord))
        else:
            xlist = [(x,x_ord * n) for x,n in xlist]
        gwordlist, rel = G.calculate_weight_zero_word(xlist, separated = True)
        counter = 0
        assert len(gwordlist) == len(oldvals)
        newdict = defaultdict(V)
        for gword, v in zip(gwordlist,oldvals):
            newv = V(v)
            for i,a in tietze_to_syllables(gword):
                oldv = V(newv)
                g = G.gen(i)
                newv = (g**-a) * V(oldv) # for the next iteration
                sign = 1
                if a < 0:
                    a = -a
                    oldv = (g**a) * V(oldv)
                    sign = -1
                for j in range(a):
                    newdict[g] += ZZ(sign) * oldv
                    oldv = (g**-1) * oldv
            counter += 1
            update_progress(float(QQ(counter)/QQ(len(oldvals))),'Reducing to degree zero equivalent')
        for b, r in rel:
            newv = V(aux_element)
            for i, a in tietze_to_syllables(r):
                oldv = V(newv)
                g = G.gen(i)
                newv = (g**-a) * V(oldv)
                sign = 1
                if a < 0:
                    a = -a
                    oldv = (g**a) * V(oldv)
                    sign = -1
                for j in range(a):
                    newdict[g] += ZZ(sign) * ZZ(b) * oldv
                    oldv = (g**-1) * oldv
        verbose('Done zero_degree_equivalent')
        ans = HH(newdict)
        if not ans.is_degree_zero_valued():
            print('!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!')
            print('The cycle is not valued in degree-zero divisors.')
            print('EXPECT THINGS TO BREAK BADLY')
            print('!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!')
        if allow_multiple:
            return ans, x_ord
        else:
            return ans

    def factor_into_generators(self,prec):
        r'''
        Use the relations:
            * gh|v = g|v + h|g^-1 v
            * g^a|v = g|(v + g^-1v + ... + g^-(a-1)v)
            * g^(-a)|v = - g^a|g^av
        '''
        V = self.parent().coefficient_module()
        G = self.parent().group()
        newdict = defaultdict(V)
        for oldg,v in self._data.items():
            newv = v
            for i,a in tietze_to_syllables(oldg.word_rep):
                g = G.gen(i)
                oldv = newv
                newv = g**-a * oldv
                sign = 1
                if a < 0:
                    a = -a
                    oldv = g**a * oldv
                    sign = -1
                for j in range(a):
                    newdict[g] += sign * oldv
                    oldv = g**-1 * oldv
                if a > 0:
                    assert oldv == newv
        return self.parent()(newdict)

    def act_by_hecke(self,l,prec,g0 = None):
        newdict = dict()
        G = self.parent().group()
        hecke_reps = G.get_hecke_reps(l,g0 = g0)
        for gk1 in hecke_reps:
            gk1inv = gk1**-1
            set_immutable(gk1inv)
            gk1inv0 = G.embed(gk1inv, prec)
            for g,v in self._data.items():
                ti = G.get_hecke_ti(gk1,g,l,True)
                try:
                    newv = v.left_act_by_matrix(gk1inv0)
                except AttributeError:
                    newv = v
                try:
                    newdict[ti] += newv
                    if newdict[ti].is_zero():
                        del newdict[ti]
                except KeyError:
                    newdict[ti] = newv
        ans = self.parent()(newdict)
        return ans

    def is_cycle(self,return_residue = False):
        res = self.parent().coefficient_module()(0)
        for g, v in self:
            res += (g**-1) * v - v
        if res.is_zero():
            ans = True
        else:
            ans = False
        return ans if return_residue == False else (ans,res)

    def hecke_smoothen(self,r,prec = None):
        if prec is None:
            prec = self.parent().coefficient_module().base_ring().precision_cap()
        rnorm = r
        try:
            rnorm = r.norm()
        except AttributeError: pass
        return self.act_by_hecke(r,prec = prec) - self.mult_by(ZZ(rnorm + 1))

    def act_by_poly_hecke(self,r,f,prec = None):
        if f == 1:
            return self
        if prec is None:
            prec = self.parent().coefficient_module().base_ring().precision_cap()
        facts = f.factor()
        if len(facts) == 1:
            verbose('Acting by f = %s and r = %s'%(f.factor(),r))
            x = f.parent().gen()
            V = [ZZ(o) for o in f.coefficients(sparse = False)]
            ans = self.mult_by(V[-1])
            for c in reversed(V[:-1]):
                ans = ans.act_by_hecke(r,prec = prec)
                ans += self.mult_by(c)
            return ans
        else:
            f0 = facts[0][0]
            ans = self.act_by_poly_hecke(r,f0,prec = prec)
            for i in range(facts[0][1]-1):
                ans = ans.act_by_poly_hecke(r,f0,prec = prec)
            for f0,e in facts[1:]:
                for i in range(e):
                    ans = ans.act_by_poly_hecke(r,f0,prec = prec)
            return ans

class OneChains(TensorProduct):
    Element = OneChainsElement
    def _repr_(self):
        return 'Group of 1-chains on %s with values in %s'%(self.group(), self.coefficient_module())


def get_homology_kernel(self, hecke_data = None):
    verbose('Entering get_homology_kernel...')
    verb = get_verbose()
    set_verbose(0)
    if hecke_data is None:
        hecke_data = []
    wp = self.wp()
    Gn = self.Gn
    ZZ1 = ZZ**1
    self.Gn._unset_coercions_used()
    self.Gn.register_action(TrivialAction(self.Gn, ZZ1))
    self.Gpn._unset_coercions_used()
    self.Gpn.register_action(TrivialAction(self.Gpn, ZZ1))
    self.Gpn.B._unset_coercions_used()
    self.Gpn.B.register_action(TrivialAction(self.Gpn.B, ZZ1))
    B = ArithHomology(self, ZZ1)
    C = HomologyGroup(Gn, ZZ1)
    group = B.group()
    Bsp = B.space()
    def phif(x):
        ans = C(0)
        for g, v in zip(group.gens(), x.values()):
            if not self.use_shapiro():
                ans += C((Gn(g), v))
            else:
                for a, ti in zip(v.values(), self.coset_reps()):
                    # We are considering a * (g tns t_i)
                    g0, _ = self.get_coset_ti( set_immutable(ti * g.quaternion_rep ))
                    ans += C((Gn(g0), a))
        return ans
    f = Bsp.hom([vector(C(phif(o))) for o in B.gens()])
    def phig(x):
        ans = C(0)
        for g, v in zip(group.gens(), x.values()):
            if not self.use_shapiro():
                ans += C((Gn(wp**-1 * g.quaternion_rep * wp), v))
            else:
                for a, ti in zip(v.values(), self.coset_reps()):
                    # We are considering a * (g tns t_i)
                    g0, _ = self.get_coset_ti( set_immutable(ti * g.quaternion_rep ))
                    ans += C((Gn(wp**-1 * g0 * wp), a))
        return ans
    g = Bsp.hom([vector(C(phig(o))) for o in B.gens()])
    maplist = [f, g]

    R = QQ['x']
    for ell, f_ell_0 in hecke_data:
        f_ell = R(f_ell_0)
        Aq = B.hecke_matrix(ell, with_torsion = True)
        tmap = Bsp.hom([sum([ZZ(a) * o for a, o in zip(col, Bsp.gens())]) for col in f_ell(Aq).columns()])
        maplist.append(tmap)
    fg = direct_sum_of_maps(maplist)
    ker = fg.kernel()
    try:
        kerV = ker.V()
        good_ker = [o.lift() for o,inv in zip(ker.gens(), ker.invariants()) if inv == 0]
    except AttributeError:
        kerV = ker
        try:
            good_ker = [kerV.lift(o) for o in ker.gens()]
        except AttributeError:
            good_ker = ker.gens()
    kerVZ_amb = ZZ**(kerV.ambient_module().dimension())
    kerVZ = kerVZ_amb.submodule([kerVZ_amb(o.denominator() * o) for o in kerV.basis()])
    good_ker = kerVZ.span_of_basis([kerVZ((o.denominator() * o).change_ring(ZZ)) for o in good_ker])
    good_ker = [B(o.denominator() * o) for o in good_ker.LLL().rows()]
    set_verbose(verb)
    verbose('Done with get_homology_kernel')
    return good_ker

def inverse_shapiro(self, x):
    if not self.use_shapiro():
        return [(g, ZZ(v[0])) for g, v in zip(self.Gpn.gens(), x.values())]
    ans = []
    for g, v in zip(self.Gn.gens(), x.values()):
        for a, ti in zip(v.values(), self.coset_reps()):
            if a[0] != 0:
                # We are considering a * (g tns t_i)
                g0, _ = self.get_coset_ti(set_immutable(ti * g.quaternion_rep))
                ans.append((self.Gn(g0), ZZ(a[0])))
    return ans
