######################
##                  ##
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
from sigma0 import Sigma0,Sigma0ActionAdjuster
from util import *
import os
import operator
from sage.rings.arith import GCD


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
        return self.__class__(self,{self.group()._an_element() : self._coeffmodule._an_element_()})

    def _repr_(self):
        return 'Homology Group'

    def group(self):
        return self._group

    def coefficient_module(self):
        return self._coeffmodule

    def _element_constructor_(self,data):
        if isinstance(data, dict):
            return self.__class__(self,data)
        else:
            return self.__class__(self, {data : ZZ(1)})

    def _coerce_map_from_(self,S):
        if isinstance(S, self.__class__):
            return S.group() is self.group() and S.coefficient_module() is self.coefficient_module()
        else:
            return False

class OneChains_element(ModuleElement):
    def __init__(self, parent, data, check = False):
        r'''
        Define an element of `H_1(G,V)`
            - data: a list

        TESTS:

        '''
        if not isinstance(data,dict):
            raise ValueError,'data should be a dictionary indexed by elements of ArithGroup'
        self._data = data
        ModuleElement.__init__(self,parent)
        if check:
            if not self.is_cycle():
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
            mystr += '{%s}|(%s)'%(str(g),v)
        return mystr

    def _add_(self,right):
        newdict = dict()
        for g,v in chain(self._data.iteritems(),right._data.iteritems()):
            try:
                newdict[g] += v
                if newdict[g].is_zero():
                    del newdict[g]
            except KeyError:
                newdict[g] = v
        return self.__class__(self.parent(),newdict)

    def _sub_(self,right):
        newdict = dict(self._data)
        for g,v in right._data.iteritems():
            try:
                newdict[g] -= v
                if newdict[g].is_zero():
                    del newdict[g]
            except KeyError:
                newdict[g] = -v
        return self.__class__(self.parent(),newdict)

    def short_rep(self):
        return [(len(g.word_rep),v.degree(),v.size()) for g,v in self._data.iteritems()]

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
        abxlist = [n * Gab(x) for x,n in xlist]
        sum_abxlist = sum(abxlist)
        x_ord = sum_abxlist.order()
        if x_ord == Infinity or (x_ord > 1 and not allow_multiple):
            raise ValueError('Must yield torsion element in abelianization (%s)'%(sum_abxlist))
        else:
            xlist = [(x,x_ord * n) for x,n in xlist]
        gwordlist, rel = G.calculate_weight_zero_word(xlist)
        gwordlist.append(rel)
        oldvals.append(V(V.base_field().gen()))
        counter = 0
        assert len(gwordlist) == len(oldvals)
        newdict = defaultdict(V)
        for gword, v in zip(gwordlist,oldvals):
            newv = V(v)
            for i,a in gword:
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
            gword = oldg.word_rep
            newv = v
            for i,a in gword:
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
        return self.__class__(self.parent(),newdict)

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
                newv = v.left_act_by_matrix(gk1inv0)
                try:
                    newdict[ti] += newv
                    if newdict[ti].is_zero():
                        del newdict[ti]
                except KeyError:
                    newdict[ti] = newv
        ans = self.__class__(self.parent(),newdict)
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

    def hecke_smoothen(self,r,prec = 20):
        rnorm = r
        try:
            rnorm = r.norm()
        except AttributeError: pass
        return self.act_by_hecke(r,prec = prec) - self.mult_by(ZZ(rnorm + 1))

    def act_by_poly_hecke(self,r,f,prec = 20):
        if f == 1:
            return self
        facts = f.factor()
        if len(facts) == 1:
            verbose('Acting by f = %s and r = %s'%(f.factor(),r))
            x = f.parent().gen()
            V = f.coefficients(sparse = False)
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
        return self.__class__(self.parent(),newdict)
