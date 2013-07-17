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
from sigma0 import Sigma0,Sigma0ActionAdjuster
from sage.structure.parent import Parent
from sage.categories.action import Action
from util import *
import os
from ocmodule import *
import operator

class Divisors(Parent):
    def __init__(self,field):
        self._field = field
        Parent.__init__(self)

    def _an_element_(self):
        return Divisor_element(self,[(3,self._field._an_element_())])

    def _element_constructor_(self,data,ptdata = None):
        return Divisor_element(self,data,ptdata)

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

# Returns a hash of an element of Cp (which is a quadratic extension of Qp)
def _hash(x):
    # ans = x._ntl_rep_abs()
    # tmp = (ZZ(ans[0][0]),ZZ(ans[0][1]))
    # return hash((tmp,ans[1]))
    return hash((x.trace(),x.norm()))


class Divisor_element(ModuleElement):
    def __init__(self,parent,data,ptdata = None):
        r'''
        A Divisor is given by a list of pairs (P,nP), where P is a point, and nP is an integer.

        TESTS:

            sage: Cp.<g> = Qq(5^3,20)
            sage: Div = Divisors(Cp)
            sage: D1 = Div(g+3)
            sage: D2 = Div(2*g+1)
            sage: D = D1 + D2
            sage: print -D
            sage: print 2*D1 + 5*D2
        '''
        self._data = defaultdict(ZZ)
        self._ptdict = {}
        ModuleElement.__init__(self,parent)
        if data == 0:
            return
        elif isinstance(data,list):
            for n,P in data:
                if n == 0:
                    continue
                hP = _hash(P)
                self._data[hP] += n
                if self._data[hP] == 0:
                    del self._data[hP]
                    del self._ptdict[hP]
                else:
                    self._ptdict[hP] = P
        elif isinstance(data,dict) and ptdata is not None:
            self._data.update(data)
            self._ptdict.update(ptdata)
        else:
            P = self.parent().base_field()(data)
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
        for P,n in self._data.iteritems():
            if not is_first:
                mystr += ' + '
            else:
                is_first = False
            mystr += '%s*(%s)'%(n,self._ptdict[P])
        return mystr

    def __cmp__(self,right):
        return self._data.__cmp__(right._data)

    def is_zero(self):
        return all((n == 0 for n in self._data.itervalues()))

    def _add_(self,right):
        newdict = defaultdict(ZZ)
        newdict.update(self._data)
        newptdata = {}
        newptdata.update(self._ptdict)
        for P,n in right._data.iteritems():
            newdict[P] += n
            if newdict[P] == 0:
                del newdict[P]
                del newptdata[P]
            else:
                newptdata[P] = right._ptdict[P]
        return self.__class__(self.parent(),newdict,ptdata = newptdata)

    def _sub_(self,right):
        newdict = defaultdict(ZZ)
        newdict.update(self._data)
        newptdata = {}
        newptdata.update(self._ptdict)
        for P,n in right._data.iteritems():
            newdict[P] -= n
            if newdict[P] == 0:
                del newdict[P]
                del newptdata[P]
            else:
                newptdata[P] = right._ptdict[P]
        return self.__class__(self.parent(),newdict,ptdata = newptdata)

    def _neg_(self):
        newdict = defaultdict(ZZ)
        newdict.update(self._data)
        newptdata = {}
        newptdata.update(self._ptdict)
        for P,n in newdict.iteritems():
            newdict[P] = -n
        return self.__class__(self.parent(),newdict,ptdata = newptdata)

    def left_act_by_matrix(self,g):
        a,b,c,d = g.list()
        gp = self.parent()
        K = self.parent().base_ring()
        newdict = {}
        newptdata = {}
        for P,n in self:
            newpt = (K(a)*P+K(b))/(K(c)*P+K(d))
            hnewpt = _hash(newpt)
            newdict[hnewpt] = n
            newptdata[hnewpt] = newpt
        return self.__class__(gp,newdict,ptdata = newptdata)

    @cached_method
    def degree(self):
        return sum(self._data.itervalues())

    @cached_method
    def size(self):
        return sum(ZZ(d).abs() for d in self._data.itervalues())

    def support(self):
        return [self._ptdict[P] for P in Set([d for d in self._data])]


class ArithGroupAction(Action):
    def __init__(self,G,M):
        Action.__init__(self,G,M,is_left = True,op = operator.mul)

    def _call_(self,g,v):
        K = v.parent().base_ring()
        iota = g.parent().get_embedding(K.precision_cap())
        a,b,c,d = iota(g.quaternion_rep).change_ring(K).list()
        newdict = defaultdict(ZZ)
        newpts = {}
        for P,n in v:
            newpt = (a*P+b)/(c*P+d)
            hp = _hash(newpt)
            newdict[hp] += n #K0(a)*P+K0(b))/(K0(c)*P+K0(d))] += n
            newpts[hp] = newpt
        return v.parent()(newdict,newpts)

class Homology(Parent):
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
        return HomologyClass(self,dict([(self.group().gen(0),self._coeffmodule._an_element_())]))

    def _repr_(self):
        return 'Homology Group'

    def group(self):
        return self._group

    def coefficient_module(self):
        return self._coeffmodule

    def _element_constructor_(self,data):
        return HomologyClass(self,data)

    def _coerce_map_from_(self,S):
        if isinstance(S,Homology):
            return S.group() is self.group() and S.coefficient_module() is self.coefficient_module()
        else:
            return False

class HomologyClass(ModuleElement):
    def __init__(self, parent, data,check = False):
        r'''
        Define an element of `H_1(G,V)`
            - data: a list

        TESTS:

            sage: G = BigArithGroup(5,6,1)
            sage: a = G([(1,2),(0,3),(2,-1)])
            sage: b = G([(1,3),(2,-1),(0,2)])
            sage: c= a^2*b^-1
            sage: rel_words = G.Gn.get_relation_words()
            sage: x = commutator(a,b)*G(rel_words[0])*commutator(c,b)*(G(rel_words[3])^-3)*commutator(a*b,c)*commutator(b,a)*G(rel_words[2])^5*commutator(a*b,c*a)
            sage: Cp.<g> = Qq(5^3,20)
            sage: Div = Divisors(Cp)
            sage: D1 = Div(g+3)
            sage: D2 = Div(2*g+1)
            sage: H1 = Homology(G,Div)
            sage: xi = H1(dict([(x,D1),(commutator(b,c),D2)]))
            sage: xi1 = xi.zero_degree_equivalent()
        '''
        if not isinstance(data,dict):
            raise ValueError,'data should be a dictionary indexed by elements of ArithGroup'
        self._data = copy(data)
        ModuleElement.__init__(self,parent)
        if check:
            if not self._check_cycle_condition():
                raise TypeError,'Element does not satisfy cycle condition'


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
            mystr += '{%s}|(%s)'%(g.quaternion_rep,v)
        return mystr

    def short_rep(self):
        return [(len(g.word_rep),v.degree(),v.size()) for g,v in self._data.iteritems()]

    def zero_degree_equivalent(self):
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
            gword = oldg._calculate_weight_zero_word()
            newv = v
            for i,a in gword:
                g = G.gen(i)
                oldv = newv
                newv = (g**-a) * oldv
                if a < 0:
                    a = -a
                    oldv = (g**a) * oldv
                    sign = -1
                else:
                    sign = 1
                for j in range(a):
                    newdict[g] += sign * oldv
                    oldv = (g**-1) * oldv
        return HomologyClass(self.parent(),newdict)

    def factor_into_generators(self):
        r'''
        Use the relations:
            * gh|v = g|v + h|g^-1 v
            * g^a|v = g|(v + g^-1v + ... + g^-(a-1)v)
            * g^(-a)|v = - g^a|g^av
        '''

        V = self.parent().coefficient_module()
        G = self.parent().group()
        newdict = defaultdict(V)
        for oldword,v in self._data.iteritems():
            gword = oldword.word_rep
            newv = v
            for i,a in gword:
                g = G.gen(i)
                oldv = newv
                newv = (g**-a) * oldv
                if a < 0:
                    a = -a
                    oldv = (g**a) * oldv
                    sign = -1
                else:
                    sign = 1
                for j in range(a):
                    newdict[g] += sign * oldv
                    oldv = (g**-1) * oldv
        return HomologyClass(self.parent(),newdict)

    def _add_(self,right):
        newdict = dict()
        for g,v in chain(self._data.iteritems(),right._data.iteritems()):
            try:
                newdict[g] += v
                if newdict[g].is_zero():
                    del newdict[g]
            except KeyError:
                newdict[g] = v
        return HomologyClass(self.parent(),newdict)

    def _sub_(self,right):
        newdict = dict(self._data)
        for g,v in right._data.iteritems():
            try:
                newdict[g] -= v
                if newdict[g].is_zero():
                    del newdict[g]
            except KeyError:
                newdict[g] = -v
        return HomologyClass(self.parent(),newdict)

    def act_by_hecke(self,l,prec):
        newdict = dict()
        G = self.parent().group()
        emb = G.get_embedding(prec)
        hecke_reps = G.get_hecke_reps(l)
        for gk1 in hecke_reps:
            for g,v in self._data.iteritems():
                ti = G.get_hecke_ti(gk1,g.quaternion_rep,l,reps = hecke_reps)
                newv = v.left_act_by_matrix(emb(gk1**-1))
                try:
                    newdict[ti] += newv
                    if newdict[ti].is_zero():
                        del newdict[ti]
                except KeyError:
                    newdict[ti] = newv
        return HomologyClass(self.parent(),newdict)#.factor_into_generators()

    def _check_cycle_condition(self):
        res = self.parent().coefficient_module()(0)
        for g,v in self._data.iteritems():
            res += (g**-1) * v - v
        if res.is_zero():
            return True
        else:
            return False

    def mult_by(self,a):
        return self.__rmul__(a)

    def hecke_smoothen(self,r,prec = 20):
        return self.act_by_hecke(r,prec = prec) - self.mult_by(r+1)

    def __rmul__(self,a):
        newdict = dict(((g,a*v) for g,v in self._data.iteritems())) if a != 0 else dict([])
        return HomologyClass(self.parent(),newdict)
