######################
##                  ##
##    ARITHMETIC    ##
##    GROUP         ##
##    ELEMENT       ##
##                  ##
######################

from sage.structure.sage_object import SageObject
from sage.misc.all import cached_method,lazy_attribute,walltime
from sage.groups.group import AlgebraicGroup
from sage.structure.element import MultiplicativeGroupElement
from sage.structure.parent import Parent
from sage.algebras.quatalg.all import QuaternionAlgebra
from sage.matrix.all import matrix,Matrix
from sage.modules.all import vector
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,NumberField,lcm,QQ,ZZ,Qp
from sage.functions.trig import arctan
from sage.misc.misc_c import prod
from collections import defaultdict
from itertools import product,chain,izip,groupby,islice,tee,starmap
from util import *
from sage.structure.sage_object import save,load
from copy import copy
from sage.misc.persist import db
from sage.modules.free_module import FreeModule_generic
from sage.functions.generalized import sgn

class ArithGroupElement(MultiplicativeGroupElement):
    def __init__(self,parent, word_rep = None, quaternion_rep = None, check = False):
        r'''
        Initialize.

        INPUT:

        - a list of the form [(g1,a1),(g2,a2),...,(gn,an)] where the gi are indices
          refering to fixed generators, and the ai are integers, or
          an element of the quaternion algebra ``self.parent().quaternion_algebra()``.

        '''
        MultiplicativeGroupElement.__init__(self, parent)
        init_data = False
        self.has_word_rep = False
        self.has_quaternion_rep = False
        if word_rep is not None:
            self.word_rep = word_rep
            self.has_word_rep = True
            init_data = True
        if quaternion_rep is not None:
            if check:
                if not parent._is_in_order(quaternion_rep):
                    raise ValueError('Quaternion (= %s) must be in order'%quaternion_rep)
                if parent.base_field() == QQ:
                    rednrm = quaternion_rep.reduced_norm() if self.parent().discriminant != 1 else quaternion_rep.determinant()
                    if rednrm != 1:
                        raise ValueError('Quaternion must be of norm 1')
                else:
                    rednrm = quaternion_rep.reduced_norm()
                    if not rednrm.is_integral() or not (1/rednrm).is_integral():
                        raise ValueError('Quaternion must be of unit norm')
                if self.has_word_rep:
                    self.check_consistency(quaternion_rep,self.word_rep)
            self.quaternion_rep = quaternion_rep
            set_immutable(self.quaternion_rep)
            self.has_quaternion_rep = True
            init_data = True
        if init_data is False:
            raise ValueError('Must pass either quaternion_rep or word_rep')
        # self._reduce_word()

    def size(self):
        return len(self.word_rep)

    @cached_method
    def __hash__(self):
        try:
            return hash((hash(self.parent()), hash(self.quaternion_rep.coefficient_tuple())))
        except (TypeError, ValueError, AttributeError):
            return hash((hash(self.parent()), hash(tuple(self.quaternion_rep.list()))))

    def _repr_(self):
        return str(self.quaternion_rep)

    def is_scalar(self):
        try:
            self.parent().base_field()(self.quaternion_rep)
            return True
        except TypeError:
            return False

    def _mul_(left,right):
        word_rep = None
        quaternion_rep = None
        # if left.has_word_rep and right.has_word_rep:
        #     word_rep = left.word_rep + right.word_rep
        if (left.has_quaternion_rep and right.has_quaternion_rep) or word_rep is None:
            quaternion_rep = left.quaternion_rep * right.quaternion_rep
        return left.__class__(left.parent(),word_rep = word_rep, quaternion_rep = quaternion_rep, check = False)

    def is_one(self):
        quatrep = self.quaternion_rep
        return quatrep == 1

    def __invert__(self):
        word_rep = None
        quaternion_rep = None
        if self.has_word_rep:
            word_rep = [-i for i in reversed(self.word_rep)]
        if self.has_quaternion_rep:
            quaternion_rep = self.quaternion_rep**(-1)
        return self.__class__(self.parent(),word_rep = word_rep, quaternion_rep = quaternion_rep, check = False)

    def __cmp__(self,right):
        selfquatrep = self.quaternion_rep
        rightquatrep = right.quaternion_rep
        if 'P' not in self.parent()._grouptype:
            return selfquatrep.__cmp__(rightquatrep)
        tmp = selfquatrep/rightquatrep
        try:
            tmp = self.parent().F(tmp)
        except TypeError:
            return 1
        if not tmp.is_integral():
            return -1
        elif not (1/tmp).is_integral():
            return 1
        else:
            return 0

    def _reduce_word(self):
        if not self.has_word_rep:
            return
        self.word_rep = reduce_word_tietze(self.word_rep)

    @lazy_attribute
    def word_rep(self):
        r'''
        Returns a word in the generators of `\Gamma` representing the given quaternion `x`.
        '''
        tmp = self.parent().get_word_rep(self.quaternion_rep)
        self.has_word_rep = True
        return tmp

    @lazy_attribute
    def quaternion_rep(self):
        r'''
        Returns the quaternion representation.
        '''
        Gamma = self.parent()
        self.has_quaternion_rep = True
        self.quaternion_rep = prod([Gamma.Ugens[g]**a for g,a in tietze_to_syllables(self.word_rep)], z = Gamma.B(1))
        set_immutable(self.quaternion_rep)
        return self.quaternion_rep

    def check_consistency(self, q = None, wd = None,txt = ''):
        if q is None and wd is None:
            if not self.has_quaternion_rep or not self.has_word_rep:
                return
        if q is None:
            q = self.quaternion_rep
        if wd is None:
            wd = self.word_rep
        Gamma = self.parent()
        F = Gamma.base_field()
        try:
            q1 = prod([Gamma.Ugens[g]**a for g,a in tietze_to_syllables(wd)],z = ZZ(1))
            quo = F(q * q1**-1)
        except (TypeError,IndexError):
            #print q
            #print q1
            print 'Inconsistency: %s'%(q * q1**-1)
            raise RuntimeError('Word and quaternion are inconsistent! (%s)'%txt)
        return

    @cached_method
    def embed(self,prec):
        assert self.has_quaternion_rep
        return self.parent().embed(self.quaternion_rep,prec)

    def conjugate_by(self, w):
        word_rep = None
        quat_rep = None
        if self.has_word_rep:
            if len(self.word_rep) == 0:
                return self
            elif len(self.word_rep) == 1:
                i = self.word_rep[0]
                if i > 0:
                    return self.parent()(w**-1 * self.parent().gen(i-1).quaternion_rep * w)
                else:
                    return self.parent()(w**-1 * self.parent().gen(-i-1).quaternion_rep * w)**-1
            else:
                word_rep = []
                for i in self.word_rep:
                    if i > 0:
                        word_rep += self.parent().gen(i-1).conjugate_by(w).word_rep
                    else:
                        word_rep += (self.parent().gen(-i-1)**-1).conjugate_by(w).word_rep
        if self.has_quaternion_rep:
            quat_rep = w**-1 * self.quaternion_rep * w
        return self.parent().element_class(self.parent(), word_rep = word_rep, quaternion_rep = quat_rep, check = False)

    def is_trivial_in_abelianization(self):
        return self.parent().abelianization()(self) == 0

    def find_bounding_cycle(self,G,npow = 1):
        r'''
        Use recursively that:
        - x^a g = a x + g - del(x^a|g) - del(x|(x + x^2 + ... + x^(a-1)))
        - x^(-a) g = -a x + g + del(1|1) + del(x^(a)|(x^-a)) - del(x^(-a)|g) + del(x|(x + x^2 + ... + x^(a-1)))
        '''
        B = G.Gn.B
        gprimeq = self.quaternion_rep
        gprime = G.Gn(gprimeq)
        gword = tietze_to_syllables(gprime.word_rep)
        rels = G.Gn._calculate_relation(G.Gn.get_weight_vector(gprime**npow),separated = True)
        # If npow > 1 then add the boundary relating self^npow with npow*self
        ans = [(-1,[gprimeq**j for j in range(1,npow)],gprime)] if npow > 1 else []

        num_terms = len(gword)
        jj = 0
        for i,a in gword:
            jj += 1
            # Decompose gword as g^a*gprime, where g is a generator
            g = G.Gn.gen(i)
            gq = g.quaternion_rep
            gaq = gq**a
            ga = g**a
            # Add the boundary relating g^a*gprime with g^a + gprime (unless we are in the last step)
            ans.extend([(-npow,[gaq],G.Gn(gword[jj:]))] if jj < num_terms else [])
            # If a < 0 use the relation g^a = -g^(-a) + del(g^a|g^(-a))
            ans.extend([(npow,[gaq**-1],ga)] if a < 0 else [])
            # By the above line we have to deal with g^a with -g^abs(a) if a <0
            # We add the corresponding boundaries, which we will substract if a > 0 and add if a < 0
            ans.extend([(-sgn(a)*npow,[gq**j for j in range(1,abs(a))],g)] if abs(a) > 1 else [])
        for m,rel in rels:
            # we deal with the relation rel^m
            # it is equivalent to deal with m*rel, because these two differ by a boundary that integrates to 1
            assert m > 0
            num_terms = len(rel)
            jj = 0
            for i,a in rel:
                jj += 1
                # we deal with a part of the relation of the form g*g'
                g = G.Gn.gen(i)
                gq = g.quaternion_rep
                ga = g**a
                gaq = gq**a
                # add the boundary relating g and g'
                ans.extend([(-m,[gaq],G.Gn(rel[jj:]))] if jj < num_terms else [])
                # If a < 0 use the relation g^a = -g^(-a) + del(g^a|g^(-a))
                ans.extend([(m,[gaq**-1],ga)] if a < 0 else [])
                # add the boundaries of g^abs(a)
                ans.extend([(-sgn(a)*m,[gq**j for j in range(1,abs(a))],g)] if abs(a) > 1 else [])
        return ans
