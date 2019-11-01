######################
##                  ##
##    GENERIC       ##
##    ARITHMETIC    ##
##    GROUP         ##
##                  ##
######################
from sage.structure.sage_object import SageObject
from sage.misc.all import cached_method,walltime
from sage.groups.group import AlgebraicGroup
from sage.structure.element import MultiplicativeGroupElement
from sage.algebras.quatalg.all import QuaternionAlgebra
from sage.matrix.all import matrix,Matrix
from sage.modules.all import vector
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,NumberField,QQ,ZZ,Qp, AA
from sage.arith.all import lcm
from sage.functions.trig import arctan
from sage.misc.misc_c import prod
from collections import defaultdict
from itertools import product,chain,izip,groupby,islice,tee,starmap
from sage.structure.sage_object import save,load
from copy import copy
from sage.misc.persist import db
from sage.modules.free_module import FreeModule_generic
from sage.functions.generalized import sgn
from sage.matrix.matrix_space import MatrixSpace
from sage.misc.sage_eval import sage_eval
from util import *
from sage.modules.fg_pid.fgp_module import FGP_Module
from sage.modular.arithgroup.congroup_sl2z import SL2Z
from sage.geometry.hyperbolic_space.hyperbolic_geodesic import HyperbolicGeodesicUHP
from sage.rings.infinity import Infinity
from arithgroup_element import ArithGroupElement

class ArithGroup_generic(AlgebraicGroup):
    Element = ArithGroupElement
    def __init__(self):
        super(ArithGroup_generic,self).__init__()

    def base_field(self):
        return self.F

    def base_ring(self):
        return self.F

    def _an_element_(self):
        return self.gen(0)

    def get_relation_words(self):
        return self._relation_words

    @cached_method
    def get_relation_matrix(self):
        # Define the (abelian) relation matrix
        rel_words = self.get_relation_words()
        relation_matrix = matrix(ZZ,len(rel_words),len(self.gens()),0)
        for i,rel in enumerate(rel_words):
            for j in rel:
                relation_matrix[i,ZZ(j).abs() - 1] += ZZ(j).sign()
        return relation_matrix

    def one(self):
        return self.element_class(self,word_rep = [],quaternion_rep = self.B(1),check = False)

    def _element_constructor_(self,x):
        if isinstance(x,int):
            if x == 0:
                return self.zero()
            elif x == 1:
                return self.one()
            else:
                raise ValueError('Wrong input')
        if isinstance(x,list):
            return self.element_class(self, word_rep = x,check = False)
        elif isinstance(x, self.element_class):
            if x.parent() is self:
                word_rep = x.word_rep if x.has_word_rep else None
                return self.element_class(self, quaternion_rep = x.quaternion_rep, word_rep = word_rep, check = False)
            elif not x.has_word_rep:
                return self.element_class(self, quaternion_rep = x.quaternion_rep, word_rep = None, check = False)
            else:
                Gx = x.parent()
                word_rep = sum((self.get_word_rep(Gx.gen(ZZ(i).abs() - 1).quaternion_rep**ZZ(i).sign()) for i in x.word_rep),[])
                return self.element_class(self, quaternion_rep = x.quaternion_rep, word_rep = word_rep, check = False)
        elif isinstance(x.parent(),FreeModule_generic):
            return self.abelianization().ab_to_G(x)
        elif x.parent() is self.B:
            return self.element_class(self, quaternion_rep = x, check = False)
        else:
            try:
                x = x.quaternion_rep
            except AttributeError: pass
            return self.element_class(self, quaternion_rep = x,check = False)

    def generate_wp_candidates(self, p, ideal_p,**kwargs):
        epsinv = matrix(QQ,2,2,[0,-1,p,0])**-1
        if self.F == QQ:
            all_elts = self.element_of_norm(ideal_p,use_magma = True,return_all = True,radius = -1, max_elements = 1)
        else:
            all_elts = self.element_of_norm(ideal_p.gens_reduced()[0],use_magma = True,return_all = True,radius = -1, max_elements = 1)
        found = False
        all_initial = all_elts
        if len(all_initial) == 0:
            raise RuntimeError('Found no initial candidates for wp')
        verbose('Found %s initial candidates for wp'%len(all_initial))
        try:
            pgen = ideal_p.gens_reduced()[0]
        except AttributeError:
            pgen = ideal_p
        for v1,v2 in cantor_diagonal(self.enumerate_elements(),self.enumerate_elements()):
            for tmp in all_initial:
                new_candidate =  v1 * tmp * v2
                yield new_candidate

    def _coerce_map_from_(self,S):
        r"""
        The only things that coerce into this group are:
        - lists
        - elements in the quaternion algebra, of reduced norm 1
        """
        if isinstance(S,list):
            return True
        return False

    def _quaternion_to_list(self,x):
        raise NotImplementedError

    def _is_in_order(self,x):
        return self._denominator(set_immutable(x)) == 1

    def _denominator(self,x):
        return lcm([ZZ(o.denominator()) for o in self._quaternion_to_list(x)])

    def _denominator_valuation(self,x,l):
        return max((o.denominator().valuation(l) for o in self._quaternion_to_list(x)))

    def quaternion_algebra(self):
        return self.B

    def enumerate_elements(self,max_length = None):
        gens = self.gens()
        Ugens = [o.quaternion_rep for o in gens] + [o.quaternion_rep**-1 for o in gens if o.quaternion_rep != 1]
        for v in enumerate_words(range(len(Ugens))):
            if max_length is not None and len(v) > max_length:
                raise StopIteration
            else:
                yield prod([Ugens[i] for i in v],self.B(1))

    @cached_method(key = lambda self, l, use_magma, g0, progress: (self, l))
    def get_hecke_reps(self,l,use_magma = True,g0 = None,progress = False): # generic
        r'''
        TESTS:

        sage: from darmonpoints.sarithgroup import ArithGroup
        sage: magma.eval('SetSeed(2000000)') #  optional - magma
        ''
        sage: G = ArithGroup(QQ,6,None,5,magma=Magma()) # optional - magma
        sage: reps = G.get_hecke_reps(11) # optional - magma
        '''
        if l == Infinity:
            reps = [self.non_positive_unit()]
        elif l == -Infinity:
            reps = [self.wp()]
        else:
            if g0 is None:
                g0 = self.element_of_norm(l,use_magma = use_magma)
            reps = [g0]
            I = self.enumerate_elements()
            n_iters = ZZ(0)
            if self.F == QQ:
                lnorm = ZZ(l).abs()
                try:
                    num_reps = lnorm if ZZ(self._O_discriminant) % lnorm == 0 else lnorm + 1
                except TypeError:
                    num_reps = lnorm if ZZ(self._O_discriminant.gen()) % ZZ(lnorm) == 0 else lnorm + 1
            else:
                lnorm = self.F.ideal(l).norm()
                num_reps = lnorm if self.F.ideal(l).divides(self._O_discriminant) else lnorm + 1

            while len(reps) < num_reps:
                n_iters += 1
                new_candidate = next(I) * g0
                new_inv = new_candidate**-1
                if not any([self._is_in_order(new_inv * old) for old in reps]):
                    reps.append(new_candidate)
                if progress and n_iters % 100 == 0:
                    update_progress(float(len(reps))/float(num_reps),'Getting Hecke representatives (%s iterations)'%(n_iters))
            if progress:
                update_progress(float(1.0),'Getting Hecke representatives (%s iterations)'%(n_iters))
        return tuple([set_immutable(o) for o in reps])

    @cached_method
    def get_hecke_ti(self,gk1,gamma,l = None,use_magma = False, reps = None):
        r"""

        INPUT:

        - gk1 - a quaternion element of norm l
        - gamma - an element of G
        - If l is None, it is assumed to be p.

        OUTPUT:

        - t_{gk1}(gamma)

        """
        elt = gk1**-1 * gamma.quaternion_rep
        if reps is None:
            reps = self.get_Up_reps() if l is None else self.get_hecke_reps(l,use_magma = use_magma)
        for gk2 in reps:
            ti = elt * gk2
            is_in_order = self._is_in_order(ti)
            if self._is_in_order(ti):
                if l is None and self.embed(set_immutable(ti),20)[1,0].valuation() > 0: # Up
                    return self(ti)
                else:
                    return self(ti)
        verbose("ti not found. gk1 = %s, gamma = %s, l = %s"%(gk1,gamma,l))
        raise RuntimeError("ti not found. gk1 = %s, gamma = %s, l = %s"%(gk1,gamma,l))

    def gen(self,i):
        return self._gens[i]

    def gens(self):
        return self._gens

    def check_word(self,delta,wd):
        Ugens = [o.quaternion_rep for o in self.gens()]
        tmp = multiply_out(wd, Ugens, self.B(1))
        assert tmp == delta,"tmp = %s, delta = %s, wd = %s"%(tmp,delta,wd)
        return wd

    def _calculate_relation(self,wt,separated = False):
        relmat = self.get_relation_matrix()
        relwords = self.get_relation_words()
        num_rels = len(relwords)
        if num_rels == 0:
            return []
        f= (ZZ**num_rels).hom(relmat.rows())
        linear_combination = f.lift(wt)
        ans = []
        for i,lam in enumerate(linear_combination):
            relation = relwords[i]
            if lam == 0:
                continue
            else:
                if separated:
                    if lam < 0:
                        ans.append((ZZ(-lam),relation))
                    else:
                        ans.append((ZZ(lam),[-j for j in reversed(relation)]))
                else:
                    if lam < 0:
                        ans += ZZ((-lam))*relation
                    else: #lam > 0
                        ans += ZZ(lam)*[-j for j in reversed(relation)]
        return ans

    def get_weight_vector(self,x):
        gens = self.gens()
        weight_vector = vector(ZZ,[0 for g in gens])
        for i in x.word_rep:
            if i > 0:
                weight_vector[i-1] += 1
            else:
                weight_vector[-i-1] -= 1
        return weight_vector

    def calculate_weight_zero_word(self, xlist, separated = False):
        Gab = self.abelianization()
        abxlist = [n * Gab(x) for x,n in xlist]
        sum_abxlist = vector(sum(abxlist))
        if not sum_abxlist == 0:
            raise ValueError('Must yield trivial element in the abelianization (%s)'%(sum_abxlist))
        oldwordlist = [copy(x.word_rep) for x,n in xlist]
        return oldwordlist, self._calculate_relation(sum(n * self.get_weight_vector(x) for x,n in xlist), separated = separated)

    def decompose_into_commutators(self,x):
        oldwordlist, rel = self.calculate_weight_zero_word([x])
        assert len(oldwordlist) == 1
        oldword = oldwordlist[0] + rel
        # At this point oldword has weight vector 0
        # We use the identity:
        # C W0 g^a W1 = C [W0,g^a] g^a W0 W1
        commutator_list = []
        for i in xrange(len(self.gens())):
            while True:
                # Find the first occurence of generator i
                try:
                    idx = [x[0] for x in oldword[1:]].index(i) + 1
                except ValueError:
                    break
                w0 = self._element_constructor_(oldword[:idx])
                gatmp = [oldword[idx]]
                ga = self._element_constructor_(gatmp)
                oldword = gatmp + oldword[:idx] + oldword[idx+1:]
                w0q = w0.quaternion_rep
                gaq = ga.quaternion_rep
                commute = w0q * gaq * w0q**-1 * gaq**-1
                if commute != 1:
                    commutator_list.append((w0,ga))
        assert len(oldword) == 0
        return commutator_list

    @cached_method
    def abelianization(self):
        from homology_abstract import Abelianization
        return Abelianization(self)
