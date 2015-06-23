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

class HomologyGroup(Parent):
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
        return self.__class__(self,dict([(self.group().gen(0),self._coeffmodule._an_element_())]))

    def _repr_(self):
        return 'Homology Group'

    def group(self):
        return self._group

    def coefficient_module(self):
        return self._coeffmodule

    def _element_constructor_(self,data):
        if isinstance(data,list):
            return self.__class__(self,data)

    def _coerce_map_from_(self,S):
        if isinstance(S,self.__class__):
            return S.group() is self.group() and S.coefficient_module() is self.coefficient_module()
        else:
            return False

class HomologyGroupElement(ModuleElement):
    def __init__(self, parent, data,check = False):
        r'''
        Define an element of `H_1(G,V)`
            - data: a list

        TESTS:

        '''
        if not isinstance(data,list):
            raise ValueError,'data should be a list of tuples (g,v), where g is in G and v in V'
        self.parse_data(data) # Need to implement
        ModuleElement.__init__(self,parent)
        if check:
            if not self._check_cycle_condition():
                raise TypeError,'Element does not satisfy cycle condition'

    def get_data(self):
        return self._data

    def _repr_(self):
        if len(self._data) == 0:
            return '0'
        return 'Homology class'
        # is_first = True
        # mystr = ''
        # for g,v in self._data.iteritems():
        #     if not is_first:
        #         mystr += ' + '
        #     else:
        #         is_first = False
        #     mystr += '{%s}|(%s)'%(str(g),v)
        # return mystr

    def _add_(self,right):
        return self.__class__(self.parent(),self._data + right._data)

    def _sub_(self,right):
        return self.__class__(self.parent(),self._data - right._data)

    def act_by_hecke(self,l,prec):
        G = self.parent().group()
        hecke_reps = G.get_hecke_reps(l)
        for gk1 in hecke_reps:
            for g,v in self._data.iteritems():
                ti = G.get_hecke_ti(gk1,g,l,hecke_reps)
                newv = v.left_act_by_matrix(G.embed(gk1**-1,prec))
                try:
                    newdict[ti] += newv
                    if newdict[ti].is_zero():
                        del newdict[ti]
                except KeyError:
                    newdict[ti] = newv
        return self.__class__(self.parent(),newdict)

    def _check_cycle_condition(self,return_residue = False):
        res = self.parent().coefficient_module()(0)
        for g,v in self._data.iteritems():
            res += (g**-1) * v - v
        if res.is_zero():
            ans = True
        else:
            ans = False
        return ans if return_residue == False else (ans,res)

    def __rmul__(self,a):
        newdict = dict(((g,a*v) for g,v in self._data.iteritems())) if a != 0 else dict([])
        return self.__class__(self.parent(),newdict)
