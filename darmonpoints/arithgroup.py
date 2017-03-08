######################
##                  ##
##    QUATERNIONIC  ##
##    ARITHMETIC    ##
##    GROUP         ##
##                  ##
######################
from sage.structure.sage_object import SageObject
from sage.misc.all import cached_method,walltime
from sage.groups.group import AlgebraicGroup
from sage.structure.element import MultiplicativeGroupElement
from sage.structure.parent import Parent
from sage.algebras.quatalg.all import QuaternionAlgebra
from sage.matrix.all import matrix,Matrix
from sage.modules.all import vector
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,NumberField,QQ,ZZ,Qp
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
from sage.rings.infinity import Infinity
from homology_abstract import HomologyGroup
from arithgroup_element import ArithGroupElement
oo = Infinity

def _get_word_jv(G,delta):
    B = delta.parent()
    CC = ComplexField(300)
    P = CC(90)/CC(100) * CC.gen()
    emb = G.get_archimedean_embedding(300)
    ngquats = G.ngquats
    gammas = G.gquats
    embgammas = G.embgquats
    pi = G.pi
    findex = G.findex
    fdargs = G.fdargs
    ans = []
    oldji = 0
    while delta != B(1):
        if delta == B(-1):
            if 'P' not in G._grouptype:
                ans += G.minus_one_long
            delta = B(1)
            continue
        z0 = act_flt_in_disc(emb(delta),CC(0),P)
        az0 = CC(z0).argument()
        if az0 < fdargs[0]:
            az0 += 2*pi
        if az0 > fdargs[-1]:
            ji = findex[0]
            embgg = embgammas[ji]
            if act_flt_in_disc(embgg,z0,P).abs() > z0.abs():
                ji = findex[1]
                embgg = embgammas[ji]
        else:
            i = next((j for j,fda in enumerate(fdargs) if az0 < fda))
            ji = findex[i+1]
            embgg = embgammas[ji]
        z0 = act_flt_in_disc(embgg,CC(0),P)
        z0abs = z0.abs()
        if ji == -oldji:
            ji = next((j for j in range(-ngquats,0) + range(1,ngquats + 1) if j != -oldji and act_flt_in_disc(embgammas[j],z0,P).abs() < z0.abs()),None)
        if ji > 0:
            gg = gammas[ji]
            newcs = G.translate[ji]
        else:
            gg = gammas[-ji]**-1
            newcs = [-o for o in reversed(G.translate[-ji])]
        delta = gg * delta
        oldji = ji
        ans = ans + newcs
    return ans


class ArithGroup_generic(AlgebraicGroup):
    def __init__(self):
        if self._compute_presentation:
            # Define the (abelian) relation matrix
            self._relation_matrix = matrix(ZZ,len(self.get_relation_words()),len(self.gens()),0)
            for i,rel in enumerate(self.get_relation_words()):
                for j in rel:
                    if j > 0:
                        self._relation_matrix[i,j-1] += 1
                    else:
                        self._relation_matrix[i,-j-1] -= 1
        self._cache_fox_gradient = dict()
        self._cache_hecke_reps = dict()

    def clear_cache(self):
        return

    def base_field(self):
        return self.F

    def base_ring(self):
        return self.F

    def _an_element_(self):
        return self.gen(0)

    def get_relation_words(self):
        return self._relation_words

    def get_relation_matrix(self):
        return self._relation_matrix

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
                if x.has_word_rep:
                    word_rep = x.word_rep
                else:
                    word_rep = None
                return self.element_class(self, quaternion_rep = x.quaternion_rep, word_rep = word_rep, check = False)
            elif not x.has_word_rep:
                return self.element_class(self, quaternion_rep = x.quaternion_rep, word_rep = None, check = False)
            else:
                word_rep = []
                Gx = x.parent()
                for i in x.word_rep:
                    if i > 0:
                        word_rep += self.get_word_rep(Gx.gen(i-1).quaternion_rep)
                    else:
                        word_rep += self.get_word_rep(Gx.gen(-i-1).quaternion_rep**-1)
                ans = self.element_class(self, quaternion_rep = x.quaternion_rep, word_rep = word_rep, check = False)
                return ans
        elif isinstance(x.parent(),FreeModule_generic):
            return self.abelianization().ab_to_G(x)
        elif x.parent() is self.B:
            return self.element_class(self, quaternion_rep = x, check = False)
        else:
            try:
                x = x.quaternion_rep
            except AttributeError:
                pass
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

    def get_archimedean_embedding(self,prec):
        r"""
        Returns an embedding of the quaternion algebra
        into the algebra of 2x2 matrices with coefficients in `\QQ_p`.

        INPUT:

        - prec -- Integer. The precision of the splitting.

        """
        I,J,K = self._splitting_at_infinity(prec)
        phi = self.F_into_RR
        def iota(q):
            R=I.parent()
            v=q.coefficient_tuple()
            return R(phi(v[0]) + phi(v[1]) * I + phi(v[2]) * J + phi(v[3]) * K)
        return iota

    def _splitting_at_infinity(self,prec):
        r"""
        Finds an embedding of the quaternion algebra
        into the algebra of 2x2 matrices with coefficients in `\RR`.

        INPUT:

        - prec -- Integer. The precision of the splitting.

        OUTPUT:

        - Matrices I, J, K giving the splitting.

        """
        if prec > self._prec_inf:
            wtime = walltime()
            verbose('Calling MatrixRing...')
            B_magma = self._B_magma
            f = self.magma.FuchsianMatrixRepresentation(B_magma.name(),Precision = prec,nvals = 1)
            verbose('Spent %s seconds in MatrixRing'%walltime(wtime))
            RR = RealField(prec)
            self._prec_inf=prec
            v = f.Image(B_magma.gen(1)).Vector()
            self._II_inf = matrix(RR,2,2,[v[i+1]._sage_() for i in xrange(4)])
            v = f.Image(B_magma.gen(2)).Vector()
            self._JJ_inf = matrix(RR,2,2,[v[i+1]._sage_() for i in xrange(4)])
            v = f.Image(B_magma.gen(3)).Vector()
            self._KK_inf = matrix(RR,2,2,[v[i+1]._sage_() for i in xrange(4)])

            RR = RealField(prec)
            rimg = f.Image(B_magma(sage_F_elt_to_magma(B_magma.BaseRing(),self.F.gen()))).Vector()
            rimg_matrix = matrix(RR,2,2,[rimg[i+1]._sage_() for i in xrange(4)])
            assert rimg_matrix.is_scalar()
            rimg = rimg_matrix[0,0]
            self.F_into_RR = self.F.hom([rimg],check = False)

        return self._II_inf, self._JJ_inf, self._KK_inf

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
        if 'P' not in self._grouptype:
            try:
                ngens = self.F_unit_offset
            except AttributeError:
                ngens = len(self.gens())
        else:
            ngens = len(self.gens())
        Ugens = [o for o in self.Ugens] + [o**-1 for o in self.Ugens if o != 1]
        for v in enumerate_words(range(2*ngens)):
            if max_length is not None and len(v) > max_length:
                raise StopIteration
            else:
                yield prod([Ugens[i] for i in v],self.B(1))

    def get_hecke_reps(self,l,use_magma = True,g0 = None,progress = False): # generic
        r'''
        TESTS:

        sage: from darmonpoints.sarithgroup import ArithGroup
        sage: magma.eval('SetSeed(2000000)') #  optional - magma
        ''
        sage: G = ArithGroup(QQ,6,None,5,magma=Magma()) # optional - magma
        sage: reps = G.get_hecke_reps(11) # optional - magma
        '''
        try:
            return self._cache_hecke_reps[l]
        except KeyError: pass
        if l == oo:
            reps = [self.non_positive_unit()]
        elif l == -oo:
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
                new_candidate = I.next() * g0
                new_inv = new_candidate**-1
                if not any([self._is_in_order(new_inv * old) for old in reps]):
                    reps.append(new_candidate)
                if progress and n_iters % 100 == 0:
                    update_progress(float(len(reps))/float(num_reps),'Getting Hecke representatives (%s iterations)'%(n_iters))
            if progress:
                update_progress(float(1.0),'Getting Hecke representatives (%s iterations)'%(n_iters))
        reps = tuple([set_immutable(o) for o in reps])
        self._cache_hecke_reps[l] = reps
        return reps

    @cached_method
    def get_hecke_ti(self,gk1,gamma,l = None,use_magma = False, conservative = False, reps = None):
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
            if l is None:
                reps = self.get_Up_reps()
            else:
                reps = self.get_hecke_reps(l,use_magma = use_magma)
        ans = None
        for gk2 in reps:
            ti = elt * gk2
            is_in_order = self._is_in_order(ti)
            if self._is_in_order(ti):
                if l is None: # Up
                    if self.embed(set_immutable(ti),20)[1,0].valuation() > 0:
                        assert ans is None
                        ans = self(ti)
                        if not conservative:
                            return ans
                else:
                    assert ans is None
                    ans = self(ti)
                    if not conservative:
                        return ans
        if ans is None:
            verbose("ti not found. gk1 = %s, gamma = %s, l = %s"%(gk1,gamma,l))
            raise RuntimeError("ti not found. gk1 = %s, gamma = %s, l = %s"%(gk1,gamma,l))
        else:
            return ans

    def gen(self,i):
        return self._gens[i]

    def gens(self):
        return self._gens

    def check_word(self,delta,wd):
        tmp = multiply_out(wd, self.Ugens, self.B(1))
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
        return Abelianization(self)

class ArithGroup_rationalquaternion(ArithGroup_generic):
    Element = ArithGroupElement
    def __init__(self,discriminant,level,info_magma = None,grouptype = None,magma = None, compute_presentation = True):
        assert grouptype in ['SL2','PSL2','PGL2'] # Need to find how to return the other groups with Voight's algorithm
        self._grouptype = grouptype
        self._compute_presentation = compute_presentation
        self.magma = magma
        self.F = QQ
        if isinstance(discriminant,list) or isinstance(discriminant,tuple):
            tmp = QuaternionAlgebra(discriminant[0],discriminant[1])
            self.abtuple = discriminant
            self.discriminant = ZZ(tmp.discriminant())
        else:
            self.discriminant = ZZ(discriminant)
        self.level = ZZ(level)

        self._prec_inf = -1

        self.__init_magma_objects(info_magma)

        self.B = QuaternionAlgebra((self._B_magma.gen(1)**2)._sage_(),(self._B_magma.gen(2)**2)._sage_())
        assert self.B.discriminant() == self.discriminant, "Error while constructing quaternion algebra"
        self.O = self.B.quaternion_order([self.B([QQ(self._O_magma.ZBasis()[n+1].Vector()[m+1]) for m in xrange(4)]) for n in xrange(4)])
        self.Obasis = self.O.basis()
        self._O_discriminant = ZZ.ideal(self.O.discriminant())
        self.basis_invmat = matrix(QQ,4,4,[list(self.O.gen(n)) for n in xrange(4)]).transpose().inverse()
        if self._compute_presentation:
            self.Ugens = [magma_quaternion_to_sage(self.B,self._B_magma(self._m2_magma.Image(self._U_magma.gen(n+1))),self.magma) for n in xrange(len(self._U_magma.gens()))]

            Uside_magma = self._G_magma.get_magma_attribute('ShimGroupSidepairs')
            mside_magma = self._G_magma.get_magma_attribute('ShimGroupSidepairsMap')
            UsideFD_magma = self._G_magma.get_magma_attribute('ShimFDSidepairs')

            self.Uside = [magma_quaternion_to_sage(self.B,self._B_magma(self._m2_magma.Image(mside_magma.Image(g))),self.magma) for g in Uside_magma.Generators()]
            self.F_unit_offset = len(self.Ugens)

            # We initialize some attributes by calling this function stupidly
            self.magma.WordProblem(self._G_magma(1))

            gquats_magma = self._G_magma.get_magma_attribute('ShimGroupSidepairsQuats')
            self.ngquats = ZZ(len(gquats_magma[1]))
            emb = self.get_archimedean_embedding(300)
            self.gquats = translate_into_twosided_list([[magma_quaternion_to_sage(self.B,self._B_magma(gquats_magma[i+1][n+1].Quaternion()),self.magma) for n in xrange(len(gquats_magma[i+1]))] for i in xrange(2)])
            self.embgquats =  [None] + [emb(g) for g in self.gquats[1:]]

            self.pi = 4 * RealField(300)(1).arctan()
            self.findex = [ZZ(x._sage_()) for x in self._G_magma.get_magma_attribute('ShimGroupSidepairsIndex')]
            self.fdargs = [RealField(300)(x._sage_()) for x in self._G_magma.get_magma_attribute('ShimFDArgs')]

            self.minus_one_long = [ len(self.Ugens) + 1 ]
            self.Ugens.append(self.B(-1))
            self.translate = [None] + [self.__magma_word_problem_jv(g**-1) for g in self.gquats[1:]]
            self._gens = [ self.element_class(self,quaternion_rep = g, word_rep = [i+1],check = False) for i,g in enumerate(self.Ugens) ]
            temp_relation_words = [self._U_magma.Relations()[n+1].LHS().ElementToSequence()._sage_() for n in xrange(len(self._U_magma.Relations()))] + [ [len(self.Ugens),len(self.Ugens)] ]
            self._relation_words = []
            for rel in temp_relation_words:
                sign = multiply_out(rel, self.Ugens, self.B(1))
                if sign == 1 or 'P' in grouptype:
                    self._relation_words.append(rel)
                else:
                    newrel = rel + self.minus_one_long
                    assert multiply_out(newrel, self.Ugens, self.B(1)) == 1
                    self._relation_words.append(newrel)
        ArithGroup_generic.__init__(self)
        Parent.__init__(self)

    def _repr_(self):
        return 'Arithmetic Group attached to rational quaternion algebra, disc = %s, level = %s'%(self.discriminant,self.level)

    def __init_magma_objects(self,info_magma = None): # Rational quaternions
        wtime = walltime()
        verbose('Calling _init_magma_objects...')
        if info_magma is None:
            QQ_magma = self.magma.RationalsAsNumberField()
            ZZ_magma = QQ_magma.MaximalOrder()
            if hasattr(self,'abtuple'):
                self._B_magma = self.magma.QuaternionAlgebra('%s'%QQ_magma.name(),self.abtuple[0],self.abtuple[1])
            else:
                self._B_magma = self.magma.QuaternionAlgebra('%s*%s'%(self.discriminant,ZZ_magma.name()))
            self._Omax_magma = self._B_magma.MaximalOrder()
            if self.level != ZZ(1):
                self._O_magma = self._Omax_magma.Order('%s*%s'%(self.level,ZZ_magma.name()))
            else:
                self._O_magma = self._Omax_magma
            self._D_magma = self.magma.UnitDisc(Precision = 300)
        else:
            ZZ_magma = info_magma._B_magma.BaseRing().Integers()
            self._B_magma = info_magma._B_magma
            self._Omax_magma = info_magma._Omax_magma
            if self.level != ZZ(1):
                self._O_magma = self._Omax_magma.Order('%s*%s'%(self.level,ZZ_magma.name()))
            else:
                self._O_magma = self._Omax_magma
            if self._compute_presentation:
                self._D_magma = self.magma.UnitDisc(Precision = 300)
            else:
                self._D_magma = info_magma._D_magma
        self._F_magma = self._B_magma.BaseRing()
        if self._compute_presentation:
            self._G_magma = self.magma.FuchsianGroup(self._O_magma.name())
            FDom_magma = self._G_magma.FundamentalDomain(self._D_magma.name())
            self._U_magma,_,self._m2_magma = self._G_magma.Group(nvals = 3)

        verbose('Spent %s seconds in init_magma_objects'%walltime(wtime))

    def _quaternion_to_list(self,x):
        return (self.basis_invmat * matrix(QQ,4,1,x.coefficient_tuple())).list()

    # rationalquaternion
    def compute_quadratic_embedding(self,K):
        QQmagma = self.magma.Rationals()
        ZZmagma = self.magma.Integers()
        a,b = self.B.invariants()
        Btmp = self.magma.QuaternionAlgebra(QQmagma,a,b)
        def quat_to_mquat(x):
            v = list(x)
            return Btmp(v[0]) + sum(v[i+1]*Btmp.gen(i+1) for i in xrange(3))
        O_magma = self.magma.QuaternionOrder(ZZmagma,[quat_to_mquat(o) for o in self.Obasis])
        K_magma = self.magma.RadicalExtension(QQmagma,2,K.discriminant()) #self._B_magma.BaseField()
        OK_magma = K_magma.MaximalOrder()
        _,iota = self.magma.Embed(OK_magma,O_magma,nvals = 2)
        mu_magma = iota.Image(OK_magma(K_magma.gen(1)))
        Bgens = list(self.B.gens())
        return magma_quaternion_to_sage(self.B,Btmp(mu_magma),self.magma)

    # rationalquaternion
    def embed_order(self,p,K,prec,outfile = None,return_all = False):
        r'''
        sage: from darmonpoints.sarithgroup import ArithGroup
        sage: G = ArithGroup(QQ,6,magma=Magma()) # optional - magma
        sage: f = G.embed_order(23,20) # optional - magma
        '''
        try:
            newobj = db('quadratic_embeddings_%s_%s.sobj'%(self.discriminant,self.level))
            mu = newobj[K.discriminant()]
        except IOError,KeyError:
            mu = self.compute_quadratic_embedding(K)

        w = K.maximal_order().ring_generators()[0]
        verbose('w is %s'%w)
        verbose('w.minpoly() = %s'%w.minpoly())
        QQp = Qp(p,prec)
        w_minpoly = w.minpoly().change_ring(QQp)
        Cp = QQp.extension(w_minpoly,names = 'g')
        r0,r1 = w.coordinates_in_terms_of_powers()(K.gen())
        v0 = K.hom([Cp(r0)+Cp(r1)*Cp.gen()])
        try:
            phi = K.hom([mu])
        except TypeError:
            phi = K.hom([mu/2])
        fwrite('# d_K = %s, h_K = %s, h_K^- = %s'%(K.discriminant(),K.class_number(),len(K.narrow_class_group())),outfile)
        fwrite('# w_K satisfies: %s'%w.minpoly(),outfile)
        assert self._is_in_order(phi(w))

        iotap = self.get_embedding(prec)
        fwrite('# Local embedding B to M_2(Q_p) sends i to %s and j to %s'%(iotap(self.B.gens()[0]).change_ring(Qp(p,5)).list(),iotap(self.B.gens()[1]).change_ring(Qp(p,5)).list()),outfile)
        a,b,c,d = iotap(mu).list()
        R = PolynomialRing(Cp,names = 'X')
        X = R.gen()
        tau1 = (Cp(a-d) + 2*v0(K.gen()))/Cp(2*c)
        tau2 = (Cp(a-d) - 2*v0(K.gen()))/Cp(2*c)

        found = False
        gamma = self(phi(K.units()[0])**2)
        fwrite('# \cO_K to R_0 given by w_K |-> %s'%phi(w),outfile)
        fwrite('# gamma_psi = %s'%gamma,outfile)
        fwrite('# tau_psi = %s'%tau1,outfile)
        fwrite('# (where g satisfies: %s)'%w.minpoly(),outfile)
        if return_all:
            return gamma,tau1,tau2
        else:
            return gamma, tau1

    def get_word_rep(self,delta): # rationalquaternion
        if not self._is_in_order(delta):
            raise RuntimeError('delta (= %s) is not in order!'%delta)
        tmp = _get_word_jv(self, delta)
        if 'P' not in self._grouptype:
            delta1 = multiply_out(tmp, self.Ugens, self.B(1))
            if delta1 != delta:
                tmp.extend(self.minus_one_long)
        return tmp

    def __magma_word_problem_jv(self,x):
        r'''
        Given a quaternion x, finds its decomposition in terms of the generators

        INPUT: x can be a list/vector of integers (giving the quaternion in terms of the basis for the order,
        or x can be a quaternion, in which case the conversion is done in the function.

        OUTPUT: A list representing a word in the generators

        EXAMPLES:

        sage: from darmonpoints.sarithgroup import ArithGroup
        sage: G = ArithGroup(QQ,7,None,15,1,magma=Magma()) # optional - magma
        sage: G.__magma_word_problem_jv(G.Ugens[2]*G.Ugens[1]) == [2,1] # optional - magma
        '''
        wtime = walltime()
        B = self.O
        x0 = x
        # If x is a quaternion, find the expression in the generators.
        if x.parent() is self.O or x.parent() is self.B:
            x = quaternion_to_magma_quaternion(self._B_magma,self.B(x))
        else:
            if len(x) != 4:
                raise ValueError('x (=%s) should be a list of length 4'%x)
            x = quaternion_to_magma_quaternion(self._B_magma,self.B(sum(a*b for a,b in zip(self.Obasis,x))))
        x_magma = self._G_magma(x)
        V = self.magma.WordProblem(x_magma).ElementToSequence()._sage_()
        delta1 = self.B(1)
        for v in V:
            delta1 = delta1 * self.Ugens[v - 1] if v > 0 else delta1 * self.Ugens[-v - 1]
        if delta1 != x0 and 'P' not in self._grouptype:
            V.extend(self.minus_one_long)
        return V

    def _fix_sign(self,x,N):
        if self.F.signature()[1] > 0:
            return x
        verbose('Fixing sign...')
        emb = self.F.embeddings(RealField(100))[0]
        try:
            N = N.gens_reduced()[0]
        except AttributeError:
            pass
        if emb(x.reduced_norm()).sign() != emb(N).sign():
            x = x * self.non_positive_unit()
        assert emb(x.reduced_norm()).sign() == emb(N).sign()
        verbose('Done fixing sign')
        return x

    def element_of_norm(self,N,use_magma = True,return_all = False,radius = -1,max_elements = -1): # in rationalquaternion
        N = ZZ(N)
        if return_all == False:
            try:
                return self._element_of_norm[N]
            except (AttributeError,KeyError):
                pass
        if not hasattr(self,'_element_of_norm'):
            self._element_of_norm  = dict([])
        force_sign = not 'P' in self._grouptype
        if use_magma:
            # assert return_all == False
            elt_magma = self._O_magma.ElementOfNorm(N * self._F_magma.Integers())
            candidate = self.B([magma_F_elt_to_sage(self.F,elt_magma.Vector()[m+1],self.magma) for m in xrange(4)])

            if force_sign:
                candidate = self._fix_sign(candidate,N)
            # assert candidate.reduced_norm() == N
            self._element_of_norm[N] = candidate
            if return_all:
                return [candidate]
            else:
                return candidate
        else:
            v = list(self.Obasis)
            verbose('Doing long enumeration...')
            M = 0
            if return_all:
                all_candidates = []
            while M != radius:
                M += 1
                verbose('M = %s,radius = %s'%(M,radius))
                verbose('v = %s'%list(v))
                for a0,an in product(range(M),product(range(-M,M+1),repeat = len(v)-1)):
                    candidate = sum((ZZ(ai) * vi for ai,vi in  zip([a0]+list(an),v)),self.B(0))
                    if candidate.reduced_norm() == N:
                        if not return_all:
                            self._element_of_norm[N] = candidate
                            return candidate
                        else:
                            self._element_of_norm[N] = candidate
                            all_candidates.append(candidate)
                            if len(all_candidates) == max_elements:
                                verbose('Found %s elements of requested norm'%len(all_candidates))
                                return all_candidates
            if return_all:
                verbose('Found %s elements of requested norm'%len(all_candidates))
                return all_candidates
            else:
                raise RuntimeError('Not found')

    def non_positive_unit(self,radius = -1):
        try:
            return self._non_positive_unit
        except AttributeError:
            pass
        v = self.Obasis
        verbose('Doing long enumeration...')
        M = 0
        while M != radius:
            M += 1
            verbose('M = %s,radius = %s'%(M,radius))
            for a0,an in product(range(M),product(range(-M+1,M),repeat = len(v)-1)):
                candidate = self.B(sum(ai*vi for ai,vi in  zip([a0]+list(an),v)))
                if candidate.reduced_norm() == -1:
                    self._non_positive_unit = candidate
                    return candidate


class ArithGroup_rationalmatrix(ArithGroup_generic):
    Element = ArithGroupElement #Matrix
    def __init__(self,level,info_magma = None,grouptype = None,magma = None, compute_presentation = True):
        from sage.modular.arithgroup.congroup_gammaH import GammaH_constructor
        assert grouptype in ['SL2','PSL2']
        self._grouptype = grouptype
        self._compute_presentation = compute_presentation
        self.magma = magma
        self.F = QQ
        self.discriminant = ZZ(1)
        try:
            self.level = ZZ(level)
            self._Gamma0_farey = GammaH_constructor(self.level, 0).farey_symbol()
        except TypeError:
            self.level = ZZ(level[0])
            self.nebentypus = level[1]
            self._Gamma0_farey = GammaH_constructor(self.level, level[1]).farey_symbol()
        self.F_units = []

        self._prec_inf = -1

        self.B = MatrixSpace(QQ,2,2)
        self.Obasis = [matrix(ZZ,2,2,v) for v in [[1,0,0,0],[0,1,0,0],[0,0,self.level,0],[0,0,0,1]]]
        self._O_discriminant = ZZ.ideal(self.level)

        self.Ugens = []
        self._gens = []
        temp_relation_words = []
        I = SL2Z([1,0,0,1])
        E = SL2Z([-1,0,0,-1])
        minus_one = None
        for i,g in enumerate(self._Gamma0_farey.generators()):
            newg = self.B([g.a(),g.b(),g.c(),g.d()])
            if newg == I:
                continue
            self.Ugens.append(newg)
            self._gens.append(self.element_class(self,quaternion_rep = newg, word_rep = [i+1],check = False))
            if g.matrix()**2 == I.matrix():
                temp_relation_words.append([(i,2)])
                if minus_one is not None:
                    temp_relation_words.append([(i,-1)]+minus_one)
                minus_one = [(i,1)]
            elif g.matrix()**2 == E.matrix():
                temp_relation_words.append([(i,4)])
                if minus_one is not None:
                    temp_relation_words.append([(i,-2)]+minus_one)
                minus_one = [(i,2)]
            elif g.matrix()**3 == I.matrix():
                temp_relation_words.append([(i,3)])
            elif g.matrix()**3 == E.matrix():
                temp_relation_words.append([(i,6)])
                if minus_one is not None:
                    temp_relation_words.append([(i,-3)]+minus_one)
                minus_one = [(i,3)]
            else:
                assert g.matrix()**24 != I.matrix()
        self.F_unit_offset = len(self.Ugens)
        if minus_one is not None:
            self.minus_one_long = syllables_to_tietze(minus_one)
        self._relation_words = []
        for rel in temp_relation_words:
            sign = prod((self._gens[g].quaternion_rep**a for g,a in rel), z = self.B(1))
            if sign == self.B(1) or 'P' in grouptype:
                self._relation_words.append(syllables_to_tietze(rel))
            else:
                assert sign == self.B(-1)
                newrel = rel + tietze_to_syllables(self.minus_one_long)
                sign = prod((self._gens[g].quaternion_rep**a for g,a in newrel), z = self.B(1))
                assert sign == self.B(1)
                self._relation_words.append(syllables_to_tietze(newrel))

        ArithGroup_generic.__init__(self)
        Parent.__init__(self)

    def _repr_(self):
        return 'Matrix Arithmetic Group of level = %s'%(self.level)
        a,b,c,d = x.list()
        return [a, b, QQ(c)/self.level, d]

    def _quaternion_to_list(self,x):
        return x.list()

    def generate_wp_candidates(self,p,ideal_p,**kwargs):
        epsinv = matrix(QQ,2,2,[0,-1,p,0])**-1
        initial_wp = kwargs.get('initial_wp')
        if self.level == 1:
            try:
                ans = matrix(QQ,2,2,[0,-1,ideal_p.gens_reduced()[0],0])
            except AttributeError:
                ans = matrix(QQ,2,2,[0,-1,ideal_p,0])
            yield ans
        else:
            # Follow Atkin--Li
            if initial_wp is None:
                from sage.arith.all import xgcd
                p = ideal_p
                m = self.level
                g,w,z = xgcd(p,-m)
                ans = matrix(QQ,2,2,[p,1,p*m*z,p*w])
                all_initial = []
                for t in sorted(range(-8,7)):
                    g, tinv, k = xgcd(t, -p * m)
                    if g == 1:
                        new_initial =  ans * matrix(QQ,2,2,[t, k, p*m, tinv])
                        all_initial.append(new_initial)
            else:
                all_initial = [initial_wp]
            for v1,v2 in cantor_diagonal(self.enumerate_elements(),self.enumerate_elements()):
                for tmp in all_initial:
                    yield  v1 * tmp * v2

    # rationalmatrix
    def embed_order(self,p,K,prec,orientation = None, use_magma = True,outfile = None, return_all = False, extra_conductor = 1):
        from limits import _find_initial_embedding_list,find_optimal_embeddings,order_and_unit
        M = self.level
        extra_conductor = ZZ(extra_conductor)
        r = K.gen()
        w = K.maximal_order().ring_generators()[0]
        r0,r1 = w.coordinates_in_terms_of_powers()(K.gen())
        QQp = Qp(p,prec)
        Cp = QQp.extension(w.minpoly(),names = 'g')
        v0 = K.hom([r0+r1*Cp.gen()])
        W = find_optimal_embeddings(K,use_magma = use_magma, extra_conductor = extra_conductor)[0]
        OD,u = order_and_unit(K, extra_conductor)
        wD = OD.ring_generators()[0]
        wDvec = w.coordinates_in_terms_of_powers()(wD)
        WD = wDvec[0] + wDvec[1] * W
        tau, gamma = _find_initial_embedding_list(v0, M, WD, orientation, OD, u)[0]
        gamma.set_immutable()
        return self(gamma), v0(tau)

    def embed_order_legacy(self,p,K,prec,outfile = None,return_all = False):
        r'''
        '''
        from limits import _find_initial_embedding_list,find_optimal_embeddings,order_and_unit, find_the_unit_of

        verbose('Computing quadratic embedding to precision %s'%prec)
        mu = find_optimal_embeddings(K,use_magma = True, extra_conductor = 1)[-1]
        verbose('Finding module generators')
        w = module_generators(K)[1]
        verbose('Done')
        w_minpoly = w.minpoly().change_ring(Qp(p,prec))
        Cp = Qp(p,prec).extension(w_minpoly,names = 'g')
        wl = w.list()
        assert len(wl) == 2
        r0 = -wl[0]/wl[1]
        r1 = 1/wl[1]
        assert r0 + r1 * w == K.gen()
        padic_Kgen = Cp(r0)+Cp(r1)*Cp.gen()
        try:
            fwrite('# d_K = %s, h_K = %s, h_K^- = %s'%(K.discriminant(),K.class_number(),len(K.narrow_class_group())),outfile)
        except NotImplementedError: pass
        fwrite('# w_K satisfies: %s'%w.minpoly(),outfile)
        mu = r0 + r1*mu
        assert K.gen(0).trace() == mu.trace() and K.gen(0).norm() == mu.determinant()
        iotap = self.get_embedding(prec)
        a,b,c,d = iotap(mu).list()
        X = PolynomialRing(Cp,names = 'X').gen()
        tau1 = (Cp(a-d) + 2*padic_Kgen)/Cp(2*c)
        tau2 = (Cp(a-d) - 2*padic_Kgen)/Cp(2*c)
        assert (Cp(c)*tau1**2 + Cp(d-a)*tau1-Cp(b)) == 0
        assert (Cp(c)*tau2**2 + Cp(d-a)*tau2-Cp(b)) == 0
        u = find_the_unit_of(self.F,K)
        gammalst = u.list()
        assert len(gammalst) == 2
        gammaquatrep = self.B(gammalst[0]) + self.B(gammalst[1]) * mu
        verbose('gammaquatrep trd = %s and nrd = %s'%(gammaquatrep.trace(),gammaquatrep.determinant()))
        verbose('u trace = %s and unorm = %s'%(u.trace(),u.norm()))
        assert gammaquatrep.trace() == u.trace() and gammaquatrep.determinant() == u.norm()
        gammaq = gammaquatrep
        while True:
            try:
                gamma = self(gammaq)
                break
            except ValueError:
                gammaq *= gammaquatrep
        a, b, c, d = iotap(gamma.quaternion_rep).list()
        assert (c*tau1**2 + (d-a)*tau1 - b) == 0
        fwrite('# \cO_K to R_0 given by w_K |-> %s'%mu,outfile)
        fwrite('# gamma_psi = %s'%gamma,outfile)
        fwrite('# tau_psi = %s'%tau1,outfile)
        fwrite('# (where g satisfies: %s)'%w.minpoly(),outfile)
        if return_all:
            return gamma, tau1, tau2
        else:
            return gamma, tau1


    def get_word_rep(self,delta): # rationalmatrix
        level = self.level
        try:
            ans = list(self._Gamma0_farey.word_problem(SL2Z(delta.list()),output = 'standard'))
        except (RuntimeError,AssertionError):
            try:
                ans = list(self._Gamma0_farey.word_problem(SL2Z((-delta).list()),output = 'standard'))
            except (RuntimeError, AssertionError):
                print 'Delta = %s'%delta
                assert 0
        tmp = multiply_out(ans, self.Ugens, self.B(1))
        delta = SL2Z(delta.list())
        err = SL2Z(delta * SL2Z(tmp**-1))
        I = SL2Z([1,0,0,1])
        E = SL2Z([-1,0,0,-1])
        gens = self._Gamma0_farey.generators()
        if err == I:
            return self.check_word(delta.matrix(),ans)
        else:
            assert err == E
            ans = self.minus_one_long + ans
            return self.check_word(delta.matrix(),ans)

    def element_of_norm(self,N,use_magma = False,return_all = False, radius = None, max_elements = None, local_condition = None): # in rationalmatrix
        try:
            if return_all:
                return [self._element_of_norm[N]]
            else:
                return self._element_of_norm[N]
        except (AttributeError,KeyError):
            pass
        if not hasattr(self,'_element_of_norm'):
            self._element_of_norm  = dict([])
        candidate = self.B([N,0,0,1])
        set_immutable(candidate)
        self._element_of_norm[N] = candidate
        if return_all:
            return [candidate]
        else:
            return candidate

    def non_positive_unit(self):
        return self.B([1,0,0,-1])

    def _is_in_order(self,x):
        entries = x.list()
        if all([o.denominator() == 1 for o in entries]):
            if entries[2] % self.level == 0:
                if hasattr(self,'nebentypus'):
                    if ZZ(entries[0]) % self.level in self.nebentypus:
                        return True
                    else:
                        return False
                else:
                    return True
            else:
                return False
        else:
            return False

class FaceRel(SageObject):
    def __init__(self,center = None ,radius = None, mat = None):
        self.center = center
        self.radius = radius
        self.mat = mat

class ArithGroup_nf_quaternion(ArithGroup_generic):
    Element = ArithGroupElement
    def __init__(self,base,a,b,level,info_magma = None,grouptype =  'PSL2',magma = None,timeout = 0, compute_presentation = True):
        self.magma = magma
        if base.signature()[1] == 0:
            self.algorithm = 'jv'
            self.get_word_rep = self.get_word_rep_jv
        elif base.signature()[1] == 1:
            self.algorithm = 'aurel'
            self.get_word_rep = self.get_word_rep_aurel
        else:
            raise NotImplementedError('At most one complex place!')
        assert grouptype in ['SL2','PSL2','GL2','PGL2']
        self._prec_inf = -1

        self._grouptype = grouptype
        self._compute_presentation = compute_presentation
        self._elements_of_prime_norm = []
        self.F = base
        self.level = base.ideal(level)
        self.a,self.b = base(a),base(b)
        self.abtuple = (self.a, self.b)
        self.__init_magma_objects(info_magma)
        self.B = QuaternionAlgebra(self.F,self.a,self.b)

        if self.B.invariants() == (1,1):
            i, j, k = self.B.gens()
            Pgen = level.gens_reduced()[0]
            tmpObasis_F = [(1 + i)/2, (j+k)/2, (Pgen/2)*(j-k), (1-i)/2]
            tmpObasis = [self.F.gen()**i * o  for o in tmpObasis_F for i in range(self.F.degree())] # DEBUG
            self._O_discriminant = self.F.ideal(self.B.discriminant()) * level
        else:
            magma_ZBasis = self._O_magma.ZBasis()
            tmpObasis = [magma_quaternion_to_sage(self.B,o,self.magma) for o in magma_ZBasis]
            self._O_discriminant = magma_F_ideal_to_sage(self.F,self._O_magma.Discriminant(),self.magma)
        self.Obasis = tmpObasis
        Obasis = [[u for o in elt.coefficient_tuple() for u in o.list()] for elt in tmpObasis]
        self.basis_invmat = matrix(QQ,4*self.F.degree(),4*self.F.degree(),Obasis).transpose().inverse()

        if self._compute_presentation:
            if self.algorithm == 'aurel':
                self._init_aurel_data(timeout = timeout)
            else:
                if timeout != 0:
                    raise NotImplementedError("Timeout functionality not implemented for totally real fields")
                self._init_jv_data()
        ArithGroup_generic.__init__(self)
        Parent.__init__(self)

    def _init_jv_data(self):
        self.Ugens = [magma_quaternion_to_sage(self.B,self._B_magma(self._m2_magma.Image(self._U_magma.gen(n+1))),self.magma) for n in xrange(len(self._U_magma.gens()))]

        Uside_magma = self._G_magma.get_magma_attribute('ShimGroupSidepairs')
        mside_magma = self._G_magma.get_magma_attribute('ShimGroupSidepairsMap')
        UsideFD_magma = self._G_magma.get_magma_attribute('ShimFDSidepairs')

        self.Uside = [magma_quaternion_to_sage(self.B,self._B_magma(self._m2_magma.Image(mside_magma.Image(g))),self.magma) for g in Uside_magma.Generators()]

        # We initialize some attributes by calling this function stupidly
        self.magma.WordProblem(self._G_magma(1))

        gquats_magma = self._G_magma.get_magma_attribute('ShimGroupSidepairsQuats')
        self.ngquats = ZZ(len(gquats_magma[1]))
        emb = self.get_archimedean_embedding(300)
        self.gquats = translate_into_twosided_list([[magma_quaternion_to_sage(self.B,self._B_magma(gquats_magma[i+1][n+1].Quaternion()),self.magma) for n in xrange(len(gquats_magma[i+1]))] for i in xrange(2)])
        self.embgquats =  [None] + [emb(g) for g in self.gquats[1:]]

        self.pi = 4 * RealField(300)(1).arctan()
        self.findex = [ZZ(x._sage_()) for x in self._G_magma.get_magma_attribute('ShimGroupSidepairsIndex')]
        self.fdargs = [RealField(300)(x._sage_()) for x in self._G_magma.get_magma_attribute('ShimFDArgs')]

        self.minus_one_long = [ len(self.Ugens) + 1 ]
        self.Ugens.append(self.B(-1))

        self.translate = [None] + [self.__magma_word_problem_jv(g**-1) for g in self.gquats[1:]]

        self._gens = [ self.element_class(self,quaternion_rep = g, word_rep = [i+1],check = False) for i,g in enumerate(self.Ugens) ]

        temp_relation_words = [self._U_magma.Relations()[n+1].LHS().ElementToSequence()._sage_() for n in xrange(len(self._U_magma.Relations()))] + [ [len(self.Ugens), len(self.Ugens)] ]

        self._relation_words = []
        for rel in temp_relation_words:
            sign = multiply_out(rel,self.Ugens)
            # assert sign.abs() == 1
            if sign == 1 or 'P' in self._grouptype:
                self._relation_words.append(rel)
            else:
                newrel = rel + self.minus_one
                assert multiply_out(newrel, self.Ugens, self.B(1)) == 1
                self._relation_words.append(newrel)

    def _init_aurel_data(self,prec = 100,periodenum = 20, timeout = 0):
        verbose('Computing normalized basis')
        if 'GL' in self._grouptype:
            # raise NotImplementedError,'This implementation has bugs'
            grouptype = '"Units"'
        else:
            grouptype = '"NormOne"'
            assert 'SL' in self._grouptype
        verbose('Seed = %s'%self.magma.eval('GetSeed()'))
        verbose('Grouptype = %s, prec = %s'%(grouptype,prec))
        _,f,e = self._O_magma.NormalizedBasis(GroupType = grouptype, nvals = 3, pr = prec, PeriodEnum = periodenum, max_time = timeout)
        verbose('Done normalizedbasis')
        if f == self.magma(False):
            raise RuntimeError("Timed out (%s sec) in NormalizedBasis"%timeout)
        matlist = self.magma.GetMatrixList(f)

        self._facerels_magma = f
        self._facerels = []
        verbose('Getting precision from Magma')
        try:
            self._RR = RR = RealField((len(str(f[1].Radius)) * RealField(20)(10).log()/RealField(20)(2).log()).ceil()-13)
        except:
            self._RR = RR = RealField(100)
        verbose('Getting precision done')
        prec = RR.precision()
        CC = ComplexField(prec)
        all_complex_embs = [o for o in self.F.embeddings(CC) if o(self.F.gen()).imag() != 0]
        assert len(all_complex_embs) == 2
        vC = all_complex_embs[0]
        tmp = self.magma.InfinitePlaces(self._F_magma)[1 + self.F.signature()[0]]
        if (vC(self.F.gen(0)).imag() * self._F_magma.gen(1).Evaluate(tmp).Im()._sage_()) < 0:
            vC = all_complex_embs[1]
            assert (vC(self.F.gen(0)).imag() * self._F_magma.gen(1).Evaluate(tmp).Im()._sage_()) > 0
        self._vC = vC
        self._HH = QuaternionAlgebra(RR,-1,-1)
        ih,jh,kh = self._HH.gens()
        self._Pmat, self._Pmatinv = JtoP(self._HH,MatrixSpace(CC,2,2))
        i,j,k  = self.B.gens()
        centerlist = [self._HH(o) for o in sage_eval(self.magma.eval('[%s[i]`Center : i in [1..%s]]'%(f.name(),len(f))),{'i': ih, 'j': jh})]
        radiuslist = [RR(o) for o in sage_eval(self.magma.eval('[%s[i]`Radius : i in [1..%s]]'%(f.name(),len(f))))]
        matlist = [Matrix(self._HH,2,2,o) for o in sage_eval(self.magma.eval('[%s[i] : i in [1..%s]]'%(matlist.name(),len(f))),{'i' : ih, 'j': jh, 'k': kh})]
        self._facerels = [FaceRel(c,r,m) for c,r,m in zip(centerlist,radiuslist,matlist)]

        verbose('Computing presentation')
        G,gens = f.Presentation(e,self._O_magma,nvals = 2)
        Hm,GtoHm = self.magma.ReduceGenerators(G,nvals = 2)
        r = self.F.gen()
        i,j,k = self.B.gens()
        chunk_length = 10
        ngens = len(gens)
        assert ngens == len(G.gens())
        nchunks = (QQ(ngens)/QQ(chunk_length)).ceil()
        verbose('Done ReduceGenerators. Now calculating inverse iso for %s generators'%len(gens))
        tmp_quaternions = []
        self._simplification_iso = []
        for tt in xrange(nchunks):
            verbose('... %s/%s ...'%(tt+1,nchunks))
            i0 = tt * chunk_length + 1
            i1 = min((tt+1) * chunk_length,ngens)
            newvec = sage_eval(self.magma.eval('[ElementToSequence(Image(%s,%s.i)) : i in [%s..%s]]'%(GtoHm.name(),G.name(),i0,i1)))
            self._simplification_iso.extend(newvec)
            tmp_quaternions.extend(sage_eval(self.magma.eval('[%s[i] : i in [%s..%s]]'%(gens.name(),i0,i1)).replace('$.1','r'),{'r':r, 'i':i, 'j':j, 'k':k}))

        assert len(self._simplification_iso) == len(self._facerels), "Simplification iso and facerels have different lengths (%s != %s)"%(len(self._simplification_iso),len(self._facerels))
        verbose('Done inverse isomorphism. Now calculating Ugens for %s generators'%len(Hm.gens()))
        self.Ugens = []
        wrds = sage_eval(self.magma.eval('[ElementToSequence(%s!(%s.i)) : i in [1..%s]]'%(G.name(),Hm.name(),len(Hm.gens()))))
        for wd in wrds:
            self.Ugens.append(multiply_out(wd, tmp_quaternions, self.B(1)))
        verbose('Done calculating Ugens. Now initializing relations')
        if 'P' not in self._grouptype:
            self.F_units = self.F.unit_group()
            self.F_unit_offset = len(self.Ugens)
            self.Ugens.extend([self.B(self.F(u)) for u in self.F_units.gens()])
            temp_relation_words = [Hm.Relations()[n+1].LHS().ElementToSequence()._sage_() for n in xrange(len(Hm.Relations()))] + [ [self.F_unit_offset + i + 1] * ZZ(u.multiplicative_order()) for i,u in enumerate(self.F_units.gens()) if u.multiplicative_order() != Infinity]
            self._relation_words = []
            for rel in temp_relation_words:
                remaining_unit = self.F_units(self.F(multiply_out(rel, self.Ugens, self.B(1))))
                assert remaining_unit.multiplicative_order() != Infinity
                ulist = remaining_unit.exponents()
                newrel = rel + syllables_to_tietze([(self.F_unit_offset + i,a) for i,a in enumerate(ulist) if a != 0 ])
                assert multiply_out(newrel, self.Ugens, self.B(1)) == 1
                self._relation_words.append(newrel)
        else:
            self._relation_words = [Hm.Relations()[n+1].LHS().ElementToSequence()._sage_() for n in xrange(len(Hm.Relations()))]
        verbose('Done initializing relations. Now generators...')
        self._gens = []
        for i,g in enumerate(self.Ugens):
            self._gens.append(ArithGroupElement(self,quaternion_rep = g, word_rep = [i+1],check = False))
        verbose('Done initializing generators')


    def _repr_(self):
        return 'Arithmetic Group attached to quaternion algebra with a = %s, b = %s and level = %s'%(self.a,self.b,self.level)

    def __init_magma_objects(self,info_magma = None): # NF quaternion
        wtime = walltime()
        verbose('Calling _init_magma_objects...')
        if info_magma is None:
            Qx_magma = self.magma.PolynomialRing(self.magma.Rationals())
            xm = Qx_magma.gen(1)
            f = self.F.gen().minpoly()
            fmagma = sum([self.magma(c)*xm**i for c,i in zip(f.coefficients(),f.exponents())])
            if f.degree() == 1:
                FF_magma = self.magma.RationalsAsNumberField()
            else:
                FF_magma = self.magma.NumberField(fmagma,DoLinearExtension = True)
            self._F_magma = FF_magma
            OF_magma = FF_magma.Integers()
            am, bm = sage_F_elt_to_magma(self._F_magma,self.a),sage_F_elt_to_magma(self._F_magma,self.b)
            self._B_magma = self.magma.QuaternionAlgebra(FF_magma,am,bm)

            if self.abtuple == (1,1):
                i, j = self._B_magma.gen(1), self._B_magma.gen(2)
                k = i * j
                on = self._B_magma.One()
                self._Omax_magma = self.magma.Order([(on + i)/2, (j+k)/2, (j-k)/2, (on - i)/2, ])
                # assert self._Omax_magma.IsPrincipal()._sage_()
            else:
                self._Omax_magma = self._B_magma.MaximalOrder()
            if self.level != self.F.ideal(1):
                if self.abtuple == (1,1):
                    i, j = self._B_magma.gen(1), self._B_magma.gen(2)
                    k = i * j
                    levgen = sage_F_elt_to_magma(self._B_magma.BaseRing(), self.level.gens_reduced()[0])
                    on = self._B_magma.One()
                    self._O_magma = self.magma.Order([(on + i)/2, (j+k)/2, levgen * (j-k)/2, (on-i)/2])
                else:
                    self._O_magma = self._Omax_magma.Order(sage_F_ideal_to_magma(self._F_magma,self.level))
            else:
                self._O_magma = self._Omax_magma
            if self._compute_presentation:
                self._D_magma = self.magma.UnitDisc(Precision = 300)
        else:
            self._F_magma = info_magma._F_magma
            OF_magma = info_magma._F_magma.Integers()
            self._B_magma = info_magma._B_magma
            self._Omax_magma = info_magma._Omax_magma
            if self.level != self.F.ideal(1):
                if self.abtuple == (1,1):
                    i, j = self._B_magma.gen(1), self._B_magma.gen(2)
                    k = i * j
                    Pgen = sage_F_elt_to_magma(self._F_magma, self.level.gens_reduced()[0])
                    on = self._B_magma.One()
                    self._O_magma = self.magma.Order([(on + i)/2, (j+k)/2,  Pgen * (j-k)/2, (on-i)/2])
                else:
                    P = sage_F_ideal_to_magma(self._F_magma,info_magma.level/self.level)
                    self._O_magma = info_magma._O_magma.pMaximalOrder(P)
            else:
                self._O_magma = self._Omax_magma
            if self._compute_presentation:
                self._D_magma = self.magma.UnitDisc(Precision = 300)
            else:
                self._D_magma = info_magma._D_magma
        if self.algorithm == 'jv':
            self._F_magma = self._B_magma.BaseRing()
            if self._compute_presentation:
                self._G_magma = self.magma.FuchsianGroup(self._O_magma.name())
                FDom_magma = self._G_magma.FundamentalDomain(self._D_magma.name())
                self._U_magma,_,self._m2_magma = self._G_magma.Group(nvals = 3)

        verbose('Spent %s seconds in init_magma_objects'%walltime(wtime))

    def _quaternion_to_list(self,x):
        xlist = [u for o in x.coefficient_tuple() for u in o.list()]
        V = (self.basis_invmat * matrix(QQ,4 * self.F.degree() ,1,xlist)).list()
        return [self.F(y) for y in izip(*[iter(V)]*self.F.degree())]

    def get_word_rep_aurel(self,gamma):
        # if not self._is_in_order(gamma):
        #     raise RuntimeError,'gamma (= %s) is not in order!'%gamma
        HH = self._HH
        R = HH.base_ring()
        boundary = self._facerels
        eps = 2**-(R(HH.base_ring().precision())/R(2))
        #verbose('eps = %s'%eps)
        correct = False
        B = self.B
        deltaword = []
        gammainv = gamma**-1
        while not correct:
            z = HH(0)
            mat_gamma = self._kleinianmatrix(gammainv)
            gammaz = act_H3(mat_gamma,z)
            if len(boundary) == 0:
                raise RuntimeError('Empty boundary')
            lengthw = 0
            delta = B(1)
            while True:
                d = R(1)
                i0 = None
                for i,b in enumerate(boundary):
                    d1 = sum((o**2 for o in (gammaz - b.center).coefficient_tuple()))/b.radius**2
                    if d >= (1+eps)*d1:
                        d = d1
                        i0 = i
                        break # This might yield longer words, but should be faster!
                if i0 is None:
                    break
                gammaz = act_H3(boundary[i0].mat,gammaz)
                deltaword.append(i0+1)
                lengthw += 1
            correct = ( -(sum((o**2 for o in gammaz.coefficient_tuple()))).log(10) > 5.0)
            if not correct:
                verbose('Error in word problem:')
                verbose('gamma = %s'%gamma)
                verbose('err = %s'%-(sum((o**2 for o in gammaz.coefficient_tuple()))))
                raise RuntimeError('Error in word problem from Aurel 1')
        deltaword.reverse()
        try:
            c = sum((list(self._simplification_iso[o-1]) for o in deltaword),[])
        except IndexError:
            raise RuntimeError('Error in word problem from Aurel 2')
        return c

    def _kleinianmatrix(self,gamma):
        B = gamma.parent()
        K = gamma.parent().base_ring()
        CC = ComplexField(self._RR.precision())
        vC = self._vC
        aa,bb = [vC(o) for o in B.invariants()]
        sa = aa.sqrt()
        bsa = bb * sa
        P, Pinv = self._Pmat, self._Pmatinv
        x1,x2,x3,x4 = [vC(o) for o in gamma.coefficient_tuple()]
        hi = self._HH.gen(0)
        phi = lambda x:self._HH(x.real()) + hi * x.imag()
        m = Pinv * Matrix(CC,2,2,[x1 + x2*sa, x3 + x4*sa, x3*bb - x4*bsa, x1- x2*sa])* P
        if gamma.reduced_norm() != 1:
            scal = 1/m.determinant().sqrt()
            m *= scal
        a,b,c,d = m.apply_map(phi).list()
        hj = self._HH.gen(1)
        A = ((a+d.conjugate()) + (b-c.conjugate())*hj)
        B = ((b+c.conjugate()) + (a-d.conjugate())*hj)
        C = ((c+b.conjugate()) + (d-a.conjugate())*hj)
        D = ((d+a.conjugate()) + (c-b.conjugate())*hj)

        return Matrix(self._HH,2,2,[A,B,C,D])

    def get_word_rep_jv(self,delta):
        if not self._is_in_order(delta):
            raise RuntimeError('delta (= %s) is not in order!'%delta)
        tmp = _get_word_jv(self, delta)
        if 'P' not in self._grouptype:
            delta1 = multiply_out(tmp,self.Ugens,self.B(1)) # Should be fixed...this is not efficient
            if delta1 != delta:
                tmp.extend(self.minus_one_long)
        return tmp

    def __magma_word_problem_jv(self,x):
        r'''
        Given a quaternion x, finds its decomposition in terms of the generators

        INPUT: x can be a list/vector of integers (giving the quaternion in terms of the basis for the order,
        or x can be a quaternion, in which case the conversion is done in the function.

        OUTPUT: A list representing a word in the generators

        EXAMPLES:

        sage: from darmonpoints.sarithgroup import ArithGroup
        sage: G = ArithGroup(QQ,7,15,magma = Magma()) # optional - magma
        sage: G.__magma_word_problem_jv(G.Ugens[2]*G.Ugens[1]) == [2,1] # optional - magma
        '''
        wtime = walltime()
        x0 = x
        # If x is a quaternion, find the expression in the generators.
        if x.parent() is self.B:
            x = quaternion_to_magma_quaternion(self._B_magma,self.B(x))
        else:
            if len(x) != 4:
                raise ValueError('x (=%s) should be a list of length 4'%x)
            x = quaternion_to_magma_quaternion(self._B_magma,self.B(sum(a*b for a,b in zip(self.Obasis,x))))
        x_magma = self._G_magma(x)
        V = self.magma.WordProblem(x_magma).ElementToSequence()._sage_()
        delta1 = self.B(1)
        for v in V:
            delta1 = delta1 * self.Ugens[v - 1] if v > 0 else delta1 * self.Ugens[-v - 1]
        if delta1 != x0 and 'P' not in self._grouptype:
            V.extend(self.minus_one_long)
        return V

    def _is_in_order(self,x):
        return all([o.is_integral() for o in self._quaternion_to_list(x)])

    # nf_quaternion
    def compute_quadratic_embedding(self,K,return_generator = False):
        O_magma = self._O_magma
        F_magma = self._F_magma

        assert K.base_field() == self.F
        Fxmagma = self.magma.PolynomialRing(F_magma)
        Fxmagma.assign_names('x')
        xm = Fxmagma.gen(1)
        b = K.gen()
        f = b.minpoly()
        fm = sum([sage_F_elt_to_magma(self._F_magma,c) * xm**i for c,i in zip(f.coefficients(),f.exponents())])
        K_magma = self.magma.NumberField(fm)
        OK_magma = K_magma.MaximalOrder()
        verbose('Calling magma Embed function...')
        try:
            _,iota = self.magma.Embed(OK_magma,O_magma,nvals = 2)
        except RuntimeError:
            print 'An error ocurred!'
            print 'OK_magma = ',OK_magma
            print 'O_magma =',O_magma
            raise RuntimeError('Error while computing quadratic embedding')
        verbose('Calling magma Embed function done!')
        wm = K_magma(OK_magma.Basis()[2])
        w = K(magma_F_elt_to_sage(self.F,wm[1],self.magma) + magma_F_elt_to_sage(self.F,wm[2],self.magma) * b)
        ans = magma_integral_quaternion_to_sage(self.B,O_magma,F_magma,iota.Image(OK_magma(K_magma.gen(1))),self.magma)
        assert ans.reduced_norm() == K.gen().norm(self.F) and ans.reduced_trace() == K.gen().trace(self.F)
        ans = self.B(ans)
        if return_generator:
            verbose('w = %s, minpoly = %s'%(w,w.minpoly()))
            assert w in K.maximal_order()
            return ans,w
        else:
            return ans

    # nf_quaternion
    def embed_order(self,p,K,prec,outfile = None,return_all = False):
        r'''
        '''
        verbose('Computing quadratic embedding to precision %s'%prec)
        mu = self.compute_quadratic_embedding(K,return_generator = False)
        verbose('Finding module generators')
        w = module_generators(K)[1]
        verbose('Done')
        w_minpoly = PolynomialRing(Qp(p,prec),names = 'x')([self._F_to_local(o) for o in w.minpoly().coefficients(sparse=False)])
        verbose('w_minpoly = %s'%w_minpoly)
        Cp = Qp(p,prec).extension(w_minpoly,names = 'g')
        verbose('Cp is %s'%Cp)
        wl = w.list()
        assert len(wl) == 2
        r0 = -wl[0]/wl[1]
        r1 = 1/wl[1]
        assert r0+r1*w == K.gen()
        padic_Kgen = Cp(self._F_to_local(r0))+Cp(self._F_to_local(r1))*Cp.gen()
        try:
            fwrite('# d_K = %s, h_K = %s, h_K^- = %s'%(K.discriminant(),K.class_number(),len(K.narrow_class_group())),outfile)
        except NotImplementedError: pass
        fwrite('# w_K satisfies: %s'%w.minpoly(),outfile)
        assert K.gen(0).trace(K.base_ring()) == mu.reduced_trace() and K.gen(0).norm(K.base_ring()) == mu.reduced_norm()

        iotap = self.get_embedding(prec)
        fwrite('# Local embedding B to M_2(Q_p) sends i to %s and j to %s'%(iotap(self.B.gens()[0]).change_ring(Qp(p,5)).list(),iotap(self.B.gens()[1]).change_ring(Qp(p,5)).list()),outfile)
        a,b,c,d = iotap(mu).list()
        tau1 = (Cp(a-d) + 2*padic_Kgen)/Cp(2*c)
        tau2 = (Cp(a-d) - 2*padic_Kgen)/Cp(2*c)
        assert (Cp(c)*tau1**2 + Cp(d-a)*tau1-Cp(b)) == 0
        assert (Cp(c)*tau2**2 + Cp(d-a)*tau2-Cp(b)) == 0

        found = False
        u = find_the_unit_of(self.F,K)
        assert u.is_integral() and (1/u).is_integral()
        gammalst = u.list()
        assert len(gammalst) == 2
        gammaquatrep = self.B(gammalst[0]) + self.B(gammalst[1]) * mu
        verbose('gammaquatrep trd = %s and nrd = %s'%(gammaquatrep.reduced_trace(),gammaquatrep.reduced_norm()))
        assert gammaquatrep.reduced_trace() == u.trace(self.F) and gammaquatrep.reduced_norm() == u.norm(self.F)
        gammaq = gammaquatrep
        while True:
            try:
                gamma = self(gammaq)
                break
            except ValueError:
                gammaq *= gammaquatrep
        fwrite('# \cO_K to R_0 given by w_K |-> %s'%mu,outfile)
        fwrite('# gamma_psi = %s'%gamma,outfile)
        fwrite('# tau_psi = %s'%tau1,outfile)
        fwrite('# (where g satisfies: %s)'%w.minpoly(),outfile)
        if return_all:
            return gamma, tau1, tau2
        else:
            return gamma, tau1

    def _fix_sign(self,x,N):
        if self.F.signature()[1] == 1 or self.F.signature()[0] == 0:
            return x
        elif self.F.signature()[0] > 1:
            # raise NotImplementedError
            return x # FIXME this may not be correct
        emb = self.F.embeddings(RealField(100))[0]
        try:
            N = N.gens_reduced()[0]
        except AttributeError:
            pass
        if emb(x.reduced_norm()).sign() != emb(N).sign():
            x = x * self.non_positive_unit()
        if emb(x.reduced_norm()).sign() != emb(N).sign():
            raise RuntimeError('Error in fix_sign')
        return x

    def element_of_prime_norm(self,max_norm,radius = -1):
        v = self.Obasis
        verbose('Doing long enumeration...')
        M = 0
        F = self.B.base_ring()
        while M != radius:
            M += 1
            verbose('M = %s,radius = %s'%(M,radius))
            for a0,an in product(range(M),product(range(-M+1,M),repeat = len(v)-1)):
                candidate = self.B(sum(ai*vi for ai,vi in  zip([a0]+list(an),v)))
                candidate_norm = F(candidate.reduced_norm())
                if candidate_norm == 0:
                    continue
                if F.ideal(candidate_norm).is_prime() and candidate_norm.norm().abs() < max_norm:
                    self._elements_of_prime_norm.append(candidate)
                    yield candidate

    def element_of_norm(self,N,use_magma = True,return_all = False,radius = -1,max_elements = -1): # in nf_quaternion
        Nideal = self.F.ideal(N)
        try:
            N = N.gens_reduced()[0]
        except AttributeError:
            pass
        force_sign = not 'P' in self._grouptype
        if return_all == False:
            try:
                if use_magma:
                    if force_sign:
                        return self._fix_sign(self._element_of_norm[Nideal.gens_reduced()[0]],N)
                    else:
                        return self._element_of_norm[Nideal.gens_reduced()[0]]
                else:
                    return self._element_of_norm[N]
            except (AttributeError,KeyError):
                pass
        else:
            if radius < 0 and max_elements < 0:
                raise ValueError('Radius must be positive')

        if not hasattr(self,'_element_of_norm'):
            self._element_of_norm  = dict([])

        x = QQ['x'].gen()
        B = self.B
        F = self.B.base_ring()
        try:
            K1 = F.extension(x*x - B.invariants()[0], names = 'y1')
            phi1 = lambda z: list(z)[0] + list(z)[1] * B.gen(0)
            NK1f = K1.ideal(Nideal.gens_reduced()[0]).factor()
        except ValueError:
            NK1f = []
        try:
            K2 = F.extension(x*x - B.invariants()[1], names = 'y2')
            phi2 = lambda z: list(z)[0] + list(z)[1] * B.gen(1)
            NK2f = K2.ideal(Nideal.gens_reduced()[0]).factor()
        except ValueError:
            NK2f = []
        found_candidate = False
        if len(NK1f) == 2:
            gr = NK1f[0][0].gens_reduced()
            if len(gr) == 1:
                candidate = phi1(gr[0])
                if self._is_in_order(candidate):
                    found_candidate = True
        if not found_candidate and len(NK2f) == 2:
            gr = NK2f[0][0].gens_reduced()
            if len(gr) == 1:
                candidate = phi2(gr[0])
                if self._is_in_order(candidate):
                    found_candidate = True
        if not found_candidate:
            elt_magma = self._O_magma.ElementOfNorm(sage_F_ideal_to_magma(self._F_magma,Nideal))
            candidate = magma_quaternion_to_sage(self.B,elt_magma,self.magma)
        self._element_of_norm[Nideal.gens_reduced()[0]] = candidate
        if force_sign:
            candidate = self._fix_sign(candidate,N)
        if return_all:
            return [candidate]
        else:
            return candidate

    def non_positive_unit(self,radius = -1):
        try:
            return self._non_positive_unit
        except AttributeError:
            pass
        v = self.Obasis
        verbose('Doing long enumeration...')
        M = 0
        ideal_one = self.F.ideal(1)
        while M != radius:
            M += 1
            verbose('M = %s,radius = %s'%(M,radius))
            for a0,an in product(range(M),product(range(-M+1,M),repeat = len(v)-1)):
                candidate = self.B(sum(ai*vi for ai,vi in  zip([a0]+list(an),v)))
                if self.F.ideal(candidate.reduced_norm()) == ideal_one and candidate.reduced_norm() != 1:
                    self._non_positive_unit = candidate
                    return candidate

class Abelianization(HomologyGroup):
    def __init__(self,G):
        HomologyGroup.__init__(self, G, ZZ**1, trivial_action = True)

    def ambient(self):
        return self.space().V()

    def abelian_group(self):
        return self.space()

    def abelian_invariants(self):
        return self.space().invariants()

    def _element_constructor_(self,x):
        if isinstance(x, tuple):
            if isinstance(x[1], tuple):
                return HomologyGroup._element_constructor_(self, x)
            else:
                return HomologyGroup._element_constructor_(self, (x[0], self.coefficient_module()([x[1]])))
        elif hasattr(x,'parent') and x.parent() is self.group():
            return HomologyGroup._element_constructor_(self, (x,self.coefficient_module()([1])))
        else:
            return HomologyGroup._element_constructor_(self, x)

    def _repr_(self):
        return 'Abelianization of %s, with invariants %s'%(self.group(),self.abelian_invariants())

    def ab_to_G(self,x):
        group = self.group()
        ans = 1
        if x.parent() == self:
            for g, v in zip(self.group().gens(), x.values()):
                ans *= g**ZZ(v[0])
        return ans
