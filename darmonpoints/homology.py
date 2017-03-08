######################
##                  ##
##     HOMOLOGY     ##
##                  ##
######################
from sage.structure.sage_object import SageObject
from sage.misc.cachefunc import cached_method
import itertools
from collections import defaultdict
from sage.matrix.all import matrix,Matrix
from itertools import product,chain,izip,groupby,islice,tee,starmap
#from distributions import Distributions, Symk
from sage.structure.parent import Parent
from sage.categories.action import Action
from sage.rings.padics.factory import Qq
from sage.sets.set import Set
from util import *
import os
from ocmodule import *
import operator
from sage.rings.arith import GCD
from sage.rings.padics.precision_error import PrecisionError
from representations import *

def construct_homology_cycle(G, D, prec, hecke_poly_getter, outfile = None, max_n = None, elliptic_curve = None):
    F = G.F
    t = PolynomialRing(F, names = 't').gen()
    K = F.extension(t*t - D, names = 'beta')
    if F.degree() == 1:
        assert len(K.embeddings(RR)) == 2
    else:
        if len(F.embeddings(RR)) > 1:
            raise NotImplementedError
        elif len(F.embeddings(RR)) == 1:
            if F.degree() != 3:
                raise NotImplementedError
            assert len(K.embeddings(RR)) == 0

    # Choose the prime to do Hecke smoothen later
    q = ZZ(2)
    D = G.prime() * G.discriminant * G.level
    try:
        D = D.norm()
    except AttributeError: pass
    while D % q == 0:
        q = q.next_prime()
    if F == QQ:
        q1 = q
    else:
        q1 = F.ideal(q).factor()[0][0]

    gamma, tau1 = G.large_group().embed_order(G.prime(),K,prec,outfile = outfile,return_all = False)
    Div = Divisors(tau1.parent())
    H1 = OneChains(G.large_group(),Div)
    D1 = Div(tau1)
    ans0 = H1({gamma: D1})
    assert ans0.is_cycle()
    ans = H1({})
    ans += ans0
    # Do hecke_smoothen to kill Eisenstein part
    ans = ans.hecke_smoothen(q1,prec = prec)
    assert ans.is_cycle()
    if elliptic_curve is not None:
        if F == QQ:
            a_ell = elliptic_curve.ap(q1)
        else:
            Q = F.ideal(q1).factor()[0][0]
            a_ell = ZZ(Q.norm() + 1 - elliptic_curve.reduction(Q).count_points())
        f = hecke_poly_getter(q1)
        R = f.parent()
        x = R.gen()
        while True:
            try:
                f = R(f/(x-a_ell))
            except TypeError:
                break
        while True:
            try:
                f = R(f/(x-(q1+1)))
            except TypeError:
                break
        f0 = f.parent()(1)
        for g, e in f.factor():
            ans = ans.act_by_poly_hecke(q1,g**e,prec = prec)
            f0 *= g**e
            try:
                ans, n = ans.zero_degree_equivalent(prec = prec, allow_multiple = True)
                return ans, n * f0(a_ell), q1
            except ValueError: pass
        verbose('Passed the check!')
    # Find zero degree equivalent
    ans, n = ans.zero_degree_equivalent(prec = prec, allow_multiple = True)
    return ans, n * f(a_ell), q1

def lattice_homology_cycle(G, xlist, prec, outfile = None, smoothen = None):
    p = G.prime()
    Gn = G.large_group()
    Cp = Qq(p**2,prec,names = 'g')
    wp = G.wp()
    wpmat = (G.embed(wp,prec)**-1).change_ring(Cp)
    a,b,c,d = wpmat.list()
    tau1 = (a*Cp.gen() + b)/(c*Cp.gen() + d)
    Div = Divisors(Cp)
    H1 = OneChains(Gn,Div)
    xi1 = H1(dict([]))
    xi2 = H1(dict([]))
    for x, a in xlist:
        xi1 += H1(dict([(Gn(x.quaternion_rep), Div(tau1))])).__rmul__(a)
        xi2 += H1(dict([(Gn(wp**-1 * x.quaternion_rep * wp), Div(tau1).left_act_by_matrix(wpmat))])).__rmul__(a)
    xi10 = xi1
    xi20 = xi2
    while True:
        try:
            newxi1 = xi1.zero_degree_equivalent(prec = prec)
            newxi2 = xi2.zero_degree_equivalent(prec = prec)
            break
        except ValueError:
            xi1 = xi1 + xi10
            xi2 = xi2 + xi20
    # m = GCD(n1, n2)
    # xi1 = xi1.mult_by(ZZ(n2/m))
    # xi2 = xi2.mult_by(ZZ(n1/m))
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

class Divisor_element(ModuleElement):
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
            sage: print -D
            Divisor of degree -2
            sage: print 2*D1 + 5*D2
            Divisor of degree 7
        '''
        self._data = defaultdict(ZZ)
        self._ptdict = {}
        ModuleElement.__init__(self,parent)
        if data == 0:
            return
        elif isinstance(data,Divisor_element):
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

    def __iter__(self):
        return iter(((self._ptdict[hP],n) for hP,n in self._data.iteritems()))

    def _repr_(self):
        return 'Divisor of degree %s'%self.degree()

    def value(self):
        if len(self._data) == 0:
            return '0'
        is_first = True
        mystr = ''
        for hP,n in self._data.iteritems():
            if not is_first:
                mystr += ' + '
            else:
                is_first = False
            mystr += '%s*(%s)'%(n,self._ptdict[hP])
        return mystr

    def __cmp__(self,right):
        return self._data.__cmp__(right._data)

    def is_zero(self):
        return all((n == 0 for n in self._data.itervalues()))

    def gcd(self):
        return GCD([n for n in self._data.itervalues()])

    def _add_(self,right):
        newdict = defaultdict(ZZ)
        newdict.update(self._data)
        new_ptdata = {}
        new_ptdata.update(self._ptdict)
        new_ptdata.update(right._ptdict)
        for hP,n in right._data.iteritems():
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
        for hP,n in right._data.iteritems():
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
        for P,n in self._data.iteritems():
            newdict[P] = -n
        return self.__class__(self.parent(),newdict,ptdata = new_ptdata)

    def left_act_by_matrix(self,g):
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
        return self.__class__(gp,newdict,ptdata = new_ptdata)

    @cached_method
    def degree(self):
        return sum(self._data.itervalues())

    @cached_method
    def size(self):
        return sum(ZZ(d).abs() for d in self._data.itervalues())

    def support(self):
        return [self._ptdict[P] for P in Set([d for d in self._data])]

class Divisors(Parent):

    Element = Divisor_element

    def __init__(self,field):
        self._field = field
        Parent.__init__(self)

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

    def _call_(self,g,v):
        K = v.parent().base_ring()
        if K is ZZ:
            try:
                return v.parent()(v._data,v._ptdata)
            except AttributeError:
                return v.parent()(v)
        prec = K.precision_cap()
        G = g.parent()
        a,b,c,d = [K(o) for o in G.embed(g.quaternion_rep,prec).list()]
        newdict = defaultdict(ZZ)
        new_pts = {}
        for P,n in v:
            new_pt = (a*P+b) / (c*P+d)
            hp = _hash(new_pt)
            newdict[hp] += n
            new_pts[hp] = new_pt
            if newdict[hp] == 0:
                del newdict[hp]
                del new_pts[hp]
        return v.parent()(newdict,new_pts)

class OneChains_element(ModuleElement):
    def __init__(self, parent, data):
        r'''
        Define an element of `H_1(G,V)`
            - data: a list

        TESTS:

        '''
        if not isinstance(data,dict):
            raise ValueError,'data should be a dictionary indexed by elements of ArithGroup'
        self._data = data
        ModuleElement.__init__(self,parent)

    def get_data(self):
        return self._data.iteritems()

    def size_of_support(self):
        return len(self._data)

    def _repr_(self):
        if len(self._data) == 0:
            return '0'
        is_first = True
        mystr = ''
        for g,v in self._data.iteritems():
            if not is_first:
                mystr += ' + '
            else:
                is_first = False
            mystr += '{%s}|(%s)'%(str(g),v)
        return mystr

    def short_rep(self):
        return [(g.size(),v.degree(),v.size()) for g,v in self._data.iteritems()]

    def is_degree_zero_valued(self):
        for v in self._data.values():
            if v.degree() != 0:
                return False
        return True

    def radius(self):
        return max([0] + [v.radius() for g,v in self._data.iteritems()])

    def zero_degree_equivalent(self, prec, allow_multiple = False):
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
        oldvals = self._data.values()
        Gab = G.abelianization()
        xlist = [(g,v.degree()) for g,v in zip(self._data.keys(),oldvals)]
        abxlist = [ Gab((x,n)) for x,n in xlist]
        sum_abxlist = vector(sum(abxlist))
        x_ord = sum_abxlist.order()
        if x_ord == Infinity or (x_ord > 1 and not allow_multiple):
            raise ValueError('Must yield torsion element in abelianization (%s)'%(sum_abxlist))
        else:
            xlist = [(x,x_ord * n) for x,n in xlist]
        gwordlist, rel = G.calculate_weight_zero_word(xlist, separated = True)
        #  gwordlist.append(rel)
        # oldvals.append(V(V.base_field().gen()))
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
            newv = V(V.base_field().gen())
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
        assert ans.is_degree_zero_valued()
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
        for oldg,v in self._data.iteritems():
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

    def _add_(self,right):
        newdict = dict()
        for g,v in chain(self._data.iteritems(),right._data.iteritems()):
            try:
                newdict[g] += v
                if newdict[g].is_zero():
                    del newdict[g]
            except KeyError:
                newdict[g] = v
        return self.parent()(newdict)

    def _sub_(self,right):
        newdict = dict(self._data)
        for g,v in right._data.iteritems():
            try:
                newdict[g] -= v
                if newdict[g].is_zero():
                    del newdict[g]
            except KeyError:
                newdict[g] = -v
        return self.parent(newdict)

    def act_by_hecke(self,l,prec,g0 = None):
        newdict = dict()
        G = self.parent().group()
        hecke_reps = G.get_hecke_reps(l,g0 = g0)
        for gk1 in hecke_reps:
            gk1inv = gk1**-1
            set_immutable(gk1inv)
            gk1inv0 = G.embed(gk1inv, prec)
            for g,v in self._data.iteritems():
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
        for g,v in self._data.iteritems():
            res += (g**-1) * v - v
        if res.is_zero():
            ans = True
        else:
            ans = False
        return ans if return_residue == False else (ans,res)

    def mult_by(self,a):
        return self.__rmul__(a)

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

    def __rmul__(self,a):
        newdict = {g: a * v for g,v in self._data.iteritems()} if a != 0 else {}
        return self.parent()(newdict)

class OneChains(Parent):
    Element = OneChains_element

    def __init__(self,G,V):
        r'''
        INPUT:
        - G: an ArithGroup
        - V: a CoeffModule
        '''
        self._group = G
        self._coeffmodule = V
        Parent.__init__(self)
        V._unset_coercions_used()
        V.register_action(ArithGroupAction(G,V))
        self._populate_coercion_lists_()

    def _an_element_(self):
        return self.element_class(self,dict([(self.group().gen(0),self._coeffmodule._an_element_())]))

    def _repr_(self):
        return 'Group of 1-chains'

    def group(self):
        return self._group

    def coefficient_module(self):
        return self._coeffmodule

    def _element_constructor_(self,data):
        if isinstance(data,dict):
            return self.element_class(self,data)
        else:
            return self.element_class(self,dict([(data,ZZ(1))]))

    def _coerce_map_from_(self,S):
        if isinstance(S,self.__class__):
            return S.group() is self.group() and S.coefficient_module() is self.coefficient_module()
        else:
            return False
