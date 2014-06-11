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
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,NumberField,lcm,QQ,ZZ,Qp
from sage.functions.trig import arctan
from sage.interfaces.magma import magma
from sage.misc.misc_c import prod
from collections import defaultdict
from itertools import product,chain,izip,groupby,islice,tee,starmap
from sage.structure.sage_object import save,load
from sage.groups.finitely_presented import FinitelyPresentedGroupElement
from sage.groups.free_group import FreeGroup
from copy import copy
from sage.misc.persist import db
from sage.modules.free_module import FreeModule_generic
from sage.functions.generalized import sgn
from sage.matrix.matrix_space import MatrixSpace
from sigma0 import Sigma0,Sigma0ActionAdjuster
from arithgroup_element import ArithGroupElement
from sage.misc.sage_eval import sage_eval
from util import *

work_with_SL2 = False # If False, works in PGL2 instead

def JtoP(H,MR,p = None):
    CC = MR.base_ring()
    RR = H.base_ring()
    I = CC.gen()
    if p is None:
        p = RR(17)/RR(5) * H.gen(1) - RR(1)/RR(2) * H.gen(0) + H(RR(1)/RR(3))
    pp = p.coefficient_tuple()
    a = CC(pp[:2])
    st = CC(pp[2]).sqrt()
    stinv = st**-1
    return MR([st,a * stinv,CC(0),stinv]),MR([stinv,-a * stinv,CC(0),st])

def act_H3(g,w):
    A,B,C,D = g.list()
    HH = w.parent()
    RR = HH.base_ring()
    gw =  (A*w+B) * (C*w+D)**-1
    sqrnormgw = sum((o**2 for o in gw.coefficient_tuple()))
    assert not sqrnormgw < 0,'g = %s, w = %s\ngw = %s, sqrnorm = %s'%(g,w,gw,sqrnormgw)
    if sqrnormgw >= 1:
        gw = gw / sqrnormgw.sqrt()
        gw *= HH(1-RR(1)/RR(2)**HH.base_ring().precision())
    return gw

class ArithGroup_generic(AlgebraicGroup):
    def __init__(self):
        # Define the (abelian) relation matrix
        self._relation_matrix = matrix(ZZ,len(self.get_relation_words()),len(self.gens()),0)
        for i,rel in enumerate(self.get_relation_words()):
            for j,k in rel:
                self._relation_matrix[i,j] += k

    def base_field(self):
        return self.F

    def base_ring(self):
        return self.F

    def _an_element_(self):
        return self.gen(0)

    def check_left_coset_reps(self,V):
        r'''
        Checks that G gi != G gj for all gi,gj in V
        '''
        for i in range(len(V)):
            vi_inv = V[i]**-1
            if any([self._is_in_order(V[j] * vi_inv) for j in range(i)+range(i+1,len(V))]):
                return False
        return True

    def check_right_coset_reps(self,V):
        r'''
        Checks that gi G != gj G for all gi,gj in V
        '''
        for i in range(len(V)):
            vi_inv = V[i]**-1
            if any([self._is_in_order(vi_inv * V[j]) for j in range(i)+range(i+1,len(V))]):
                return False
        return True

    def get_relation_words(self):
        return self._relation_words

    def get_relation_matrix(self):
        return self._relation_matrix

    def one(self):
        return self.element_class(self,word_rep = [],quaternion_rep = self.B(1),check = False)

    def _element_constructor_(self,x):
        if isinstance(x,list):
            return self.element_class(self, word_rep = x,check = False)
        elif x.parent() is self.quaternion_algebra():
            return self.element_class(self, quaternion_rep = x,check = False)
        elif isinstance(x.parent(),FreeModule_generic):
            Ga, V, free_idx = self.abelianization()
            indices_vec = [Ga.gen(o).lift() for o in free_idx]
            return self.element_class(self,word_rep = [(idx,n) for indices in indices_vec for idx,n in zip(indices,x)],check = False)
        else:
            return self.element_class(self, quaternion_rep = x,check = False)

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
        def iota(q):
            R=I.parent()
            v=q.coefficient_tuple()
            return R(v[0] + I*v[1] + J*v[2] + K*v[3])
        return iota

    def _splitting_at_infinity(self,prec):
        r"""
        Finds an embedding of the definite quaternion algebra
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
            f = magma.FuchsianMatrixRepresentation(B_magma.name(),nvals = 1)
            verbose('Spent %s seconds in MatrixRing'%walltime(wtime))
            RR = RealField(prec)
            self._prec_inf=prec
            v = f.Image(B_magma.gen(1)).Vector()
            self._II_inf = matrix(RR,2,2,[v[i+1]._sage_() for i in range(4)])
            v = f.Image(B_magma.gen(2)).Vector()
            self._JJ_inf = matrix(RR,2,2,[v[i+1]._sage_() for i in range(4)])
            v = f.Image(B_magma.gen(3)).Vector()
            self._KK_inf = matrix(RR,2,2,[v[i+1]._sage_() for i in range(4)])
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
        ngens = len(self.gens())
        for v in enumerate_words(range(ngens)):
            if max_length is not None and len(v) > max_length:
                raise StopIteration
            else:
                yield prod([self.Ugens[i] for i in v])

    def get_hecke_ti(self,gk1,gamma,l, reps = None):
        r"""

        INPUT:

        - gk1 - a quaternion element of norm l
        - gamma - an element of G

        OUTPUT:

        - t_{gk1}(gamma)

        """
        elt = gk1**-1 * gamma
        found = False
        if reps is None:
            reps = self.get_hecke_reps(l)
        for gk2 in reps:
            ti = elt * gk2
            if self._is_in_order(ti):
                return self(ti)

    def gen(self,i):
        return self._gens[i]

    def gens(self):
        return self._gens

    def compute_quadratic_embedding(self,K):
        a,b = self.B.invariants() if self.discriminant != 1 else (1,1)
        QQmagma = magma.Rationals()
        ZZmagma = magma.Integers()
        Btmp = magma.QuaternionAlgebra(QQmagma,a,b)
        def quat_to_mquat(x):
            v = list(x)
            return Btmp(v[0]) + sum(v[i+1]*Btmp.gen(i+1) for i in range(3))

        O_magma = magma.QuaternionOrder(ZZmagma,[quat_to_mquat(o) for o in self.Obasis])

        #QQmagma = self._B_magma.BaseRing()#magma.RationalsAsNumberField()
        K_magma = magma.RadicalExtension(QQmagma,2,K.discriminant()) #self._B_magma.BaseField()
        OK_magma = K_magma.MaximalOrder()
        _,iota = magma.Embed(OK_magma,O_magma,nvals = 2)
        mu_magma = iota.Image(OK_magma(K_magma.gen(1)))
        Bgens = list(self.B.gens()) if self.discriminant != 1 else [matrix(QQ,2,2,[1,0,0,-1]),matrix(QQ,2,2,[0,1,1,0]),matrix(QQ,2,2,[0,1,-1,0])]
        return sum(a*b for a,b in zip([self.B(1)]+Bgens,[Btmp(mu_magma).Vector()[m+1].Norm()._sage_() for m in range(4)]))

    def embed_order(self,p,K,prec,zero_deg = True,outfile = None,return_all = False):
        r'''
        sage: G = ArithGroup(5,6,1)
        sage: f = G.embed_order(23,20)
        sage: f0 = f.zero_degree_equivalent()
        '''
        try:
            newobj = db('quadratic_embeddings_%s_%s.sobj'%(self.discriminant,self.level))
            mu = newobj[K.discriminant()]
        except IOError,KeyError:
            mu = self.compute_quadratic_embedding(K)

        w = K.maximal_order().ring_generators()[0]
        verbose('w is %s'%w)
        verbose('w.minpoly() = %s'%w.minpoly())
        Cp = Qp(p,prec).extension(w.minpoly(),names = 'g')
        r0,r1 = w.coordinates_in_terms_of_powers()(K.gen())
        v0 = K.hom([Cp(r0)+Cp(r1)*Cp.gen()])
        try:
            phi = K.hom([mu])
        except TypeError:
            phi = K.hom([mu/2])
        fwrite('d_K = %s, h_K = %s, h_K^- = %s'%(K.discriminant(),K.class_number(),len(K.narrow_class_group())),outfile)
        fwrite('w_K satisfies: %s'%w.minpoly(),outfile)
        assert self._is_in_order(phi(w))

        iotap = self.get_embedding(prec)
        fwrite('Local embedding B to M_2(Q_p) sends i to %s and j to %s'%(iotap(self.B.gens()[0]).change_ring(Qp(p,5)).list(),iotap(self.B.gens()[1]).change_ring(Qp(p,5)).list()),outfile)
        a,b,c,d = iotap(mu).list()
        R = PolynomialRing(Cp,names = 'X')
        X = R.gen()
        tau1 = (Cp(a-d) + 2*v0(K.gen()))/Cp(2*c)
        tau2 = (Cp(a-d) - 2*v0(K.gen()))/Cp(2*c)

        # assert (c*tau**2 + (d-a)*tau-b) == 0

        found = False
        gamma = self(phi(K.units()[0])**2)
        fwrite('\cO_K to R_0 given by w_K |-> %s'%phi(w),outfile)
        fwrite('gamma_psi = %s'%gamma,outfile)
        fwrite('tau_psi = %s'%tau1,outfile)
        fwrite('(where g satisfies: %s)'%w.minpoly(),outfile)
        if return_all:
            return gamma,tau1,tau2
        else:
            return gamma, tau1

    @cached_method
    def hecke_matrix(self,l):
        Gab, V, free_idx = self.abelianization()
        gens = self.gens()
        freegens = [prod(self.gen(i)**n for i,n in enumerate(Gab.gen(idx).lift().list())) for idx in free_idx]

        dim = len(freegens)
        M = matrix(ZZ,dim,dim,0)
        for j,g in enumerate(freegens):
            # Construct column j of the matrix
            newcol = self.act_by_hecke(l,g)
            M.set_column(j,newcol.list())
        return M

    def act_by_hecke(self,l,g):
        r'''
           - l:  a prime
           - g: an element of the arithmetic group
        '''
        Gab, V, free_idx = self.abelianization()
        hecke_reps = self.get_hecke_reps(l)
        return sum(self.image_in_abelianized(self.get_hecke_ti(gk1,g.quaternion_rep,l,reps=hecke_reps)) for gk1 in hecke_reps)

    def _calculate_relation(self,wt,separated = False):
        relmat = self.get_relation_matrix()
        relwords = self.get_relation_words()
        num_rels = len(relwords)
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
                        ans.append((ZZ(lam),[(g,-j) for g,j in reversed(relation)]))
                else:
                    if lam < 0:
                        ans += ZZ((-lam))*relation
                    else: #lam > 0
                        ans += ZZ(lam)*[(g,-j) for g,j in reversed(relation)]
        if separated:
            return ans
        else:
            return reduce_word(ans)

    def get_weight_vector(self,x):
        gens = self.gens()
        weight_vector = vector(ZZ,[0 for g in gens])
        for i,a in x.word_rep:
            weight_vector[i] += a
        return weight_vector

    def calculate_weight_zero_word(self,x):
        if not x.is_trivial_in_abelianization():
            raise ValueError,'Element must be trivial in the abelianization'
        oldword = copy(x.word_rep)
        oldword += self._calculate_relation(self.get_weight_vector(x))
        return reduce_word(oldword)

    def decompose_into_commutators(self,x):
        oldword = self.calculate_weight_zero_word(x)
        # At this point oldword has weight vector 0
        # We use the identity:
        # C W0 g^a W1 = C [W0,g^a] g^a W0 W1
        commutator_list = []
        for i in range(len(self.gens())):
            while True:
                # Find the first occurence of generator i
                try:
                    idx = [x[0] for x in oldword[1:]].index(i) + 1
                except ValueError:
                    break
                w0 = self._element_constructor_(oldword[:idx])
                gatmp = [oldword[idx]]
                ga = self._element_constructor_(gatmp)
                oldword = reduce_word(gatmp + oldword[:idx] + oldword[idx+1:])
                w0q = w0.quaternion_rep
                gaq = ga.quaternion_rep
                commute = w0q*gaq*w0q**-1*gaq**-1
                if commute != 1:
                    commutator_list.append((w0,ga))
        assert len(oldword) == 0
        return commutator_list

class ArithGroup_rationalquaternion(ArithGroup_generic):
    Element = ArithGroupElement
    def __init__(self,discriminant,level,info_magma = None):
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
        if self.B.discriminant() != self.discriminant:
            print 'Error while constructing quaternion algebra...'
            assert 0
        self.O = self.B.quaternion_order([self.B([QQ(self._O_magma.ZBasis()[n+1].Vector()[m+1]) for m in range(4)]) for n in range(4)])
        self.Obasis = self.O.basis()
        self._O_discriminant = ZZ.ideal(self.O.discriminant())
        self.basis_invmat = matrix(QQ,4,4,[list(self.O.gen(n)) for n in range(4)]).transpose().inverse()
        self.Ugens = [self.B([self._B_magma(self._m2_magma.Image(self._U_magma.gen(n+1))).Vector()[m+1] for m in range(4)]) for n in range(len(self._U_magma.gens()))]

        Uside_magma = self._G_magma.get_magma_attribute('ShimGroupSidepairs')
        mside_magma = self._G_magma.get_magma_attribute('ShimGroupSidepairsMap')
        UsideFD_magma = self._G_magma.get_magma_attribute('ShimFDSidepairs')

        self.Uside = [self.B([self._B_magma(self._m2_magma.Image(mside_magma.Image(g))).Vector()[m+1] for m in range(4)]) for g in Uside_magma.Generators()]

        # We initialize some attributes by calling this function stupidly
        magma.WordProblem(self._G_magma(1))

        gquats_magma = self._G_magma.get_magma_attribute('ShimGroupSidepairsQuats')
        self.ngquats = ZZ(len(gquats_magma[1]))
        emb = self.get_archimedean_embedding(300)
        self.gquats = translate_into_twosided_list([[self.B([self._B_magma(gquats_magma[i+1][n+1].Quaternion()).Vector()[m+1] for m in range(4)]) for n in range(len(gquats_magma[i+1]))] for i in range(2)])
        self.embgquats =  [None] + [emb(g) for g in self.gquats[1:]]

        self.pi = 4 * RealField(300)(1).arctan()
        self.findex = [ZZ(x._sage_()) for x in self._G_magma.get_magma_attribute('ShimGroupSidepairsIndex')]
        self.fdargs = [RealField(300)(x._sage_()) for x in self._G_magma.get_magma_attribute('ShimFDArgs')]

        if work_with_SL2:
            self.minus_one_long = [ len(self.Ugens) + 1 ]
            self.minus_one = shorten_word(self.minus_one_long)
        self.Ugens.append(self.B(-1))

        self.translate = [None] + [self.__magma_word_problem(g**-1) for g in self.gquats[1:]]

        self._gens = [ self.element_class(self,quaternion_rep = g, word_rep = [(i,1)],check = False) for i,g in enumerate(self.Ugens) ]

        temp_relation_words = [shorten_word(self._U_magma.Relations()[n+1].LHS().ElementToSequence()._sage_()) for n in range(len(self._U_magma.Relations()))] + [[(len(self.Ugens)-1,2)]]

        self._relation_words = []
        for rel in temp_relation_words:
            sign = ZZ(prod((self.Ugens[g]**a for g,a in rel), z = self.B(1)))
            if sign == 1:
                self._relation_words.append(rel)
            else:
                assert sign == -1
                if work_with_SL2:
                    newrel = rel + self.minus_one
                    sign = ZZ(prod((self.Ugens[g]**a for g,a in newrel), z = self.B(1)))
                    assert sign == 1
                    self._relation_words.append(newrel)
                else:
                    self._relation_words.append(rel)

        self.GG = FreeGroup(len(self.gens())) / [syllables_to_tietze(rel) for rel in self.get_relation_words()]

        ArithGroup_generic.__init__(self)
        Parent.__init__(self)


    def _repr_(self):
        return 'Arithmetic Group attached to rational quaternion algebra, disc = %s, level = %s'%(self.discriminant,self.level)

    def __init_magma_objects(self,info_magma = None):
        wtime = walltime()
        verbose('Calling _init_magma_objects...')
        if info_magma is None:
            QQ_magma = magma.RationalsAsNumberField()
            ZZ_magma = QQ_magma.Integers()
            if hasattr(self,'abtuple'):
                self._B_magma = magma.QuaternionAlgebra('%s'%QQ_magma.name(),self.abtuple[0],self.abtuple[1])
            else:
                self._B_magma = magma.QuaternionAlgebra('%s*%s'%(self.discriminant,ZZ_magma.name()))

            self._Omax_magma = self._B_magma.MaximalOrder()
            if self.level != ZZ(1):
                self._O_magma = self._Omax_magma.Order('%s*%s'%(self.level,ZZ_magma.name()))
            else:
                self._O_magma = self._Omax_magma
            self._D_magma = magma.UnitDisc(Precision = 300)
        else:
            ZZ_magma = info_magma._B_magma.BaseRing().Integers()
            self._B_magma = info_magma._B_magma
            self._Omax_magma = info_magma._B_magma.MaximalOrder()
            if self.level != ZZ(1):
                self._O_magma = self._Omax_magma.Order('%s*%s'%(self.level,ZZ_magma.name()))
            else:
                self._O_magma = self._Omax_magma
            self._D_magma = info_magma._D_magma
        self._G_magma = magma.FuchsianGroup(self._O_magma.name())
        FDom_magma = self._G_magma.FundamentalDomain(self._D_magma.name())
        self._U_magma,_,self._m2_magma = self._G_magma.Group(nvals = 3)

        verbose('Spent %s seconds in init_magma_objects'%walltime(wtime))

    def _quaternion_to_list(self,x):
        return (self.basis_invmat * matrix(QQ,4,1,x.coefficient_tuple())).list()

    @cached_method
    def get_word_rep(self,delta):
        if not self._is_in_order(delta):
            raise RuntimeError,'delta (= %s) is not in order!'%delta
        try:
            c = self._get_word_recursive(delta,0)
        except RuntimeError:
            verbose('!! Resorted to Magma, indicates a bug (delta = %s,norm = %s)!!'%(delta,delta.reduced_norm()))
            c = self.__magma_word_problem(delta)
        tmp = [(g-1,len(list(a))) if g > 0 else (-g-1,-len(list(a))) for g,a in groupby(c)] # shorten_word(c)
        if work_with_SL2:
            delta1 =  prod((self.Ugens[g]**a for g,a in tmp)) # Should be fixed...this is not efficient
            if delta1 != delta:
                tmp.extend(self.minus_one)
                delta1 =  prod((self.Ugens[g]**a for g,a in tmp)) # Should be fixed...this is not efficient
                assert delta1 == delta
        return tmp

    @cached_method
    def _get_word_recursive(self,delta,oldji,depth = 0):
        if depth > 1000:
            raise RuntimeError
        B = delta.parent()
        if delta == B(1):
            return []
        elif delta == B(-1):
            if work_with_SL2:
                return self.minus_one_long
            else:
                return []
        else:
            CC = ComplexField(300)
            P = CC(91)/CC(100) * CC.gen()
            emb = self.get_archimedean_embedding(300)
            ngquats = self.ngquats
            gammas = self.gquats
            embgammas = self.embgquats
            pi = self.pi

            findex = self.findex
            fdargs = self.fdargs
            z0 = act_flt_in_disc(emb(delta),CC(0),P)
            az0 = CC(z0).argument()
            if az0 < fdargs[0]:
                az0 += 2*pi
            if az0 > fdargs[-1]:
                ji = findex[0]
                embgg = embgammas[ji]
                if act_flt_in_disc(embgg,z0,P).abs() >= z0.abs():
                    ji = findex[1]
                    embgg = embgammas[ji]
            else:
                i = next((j for j,fda in enumerate(fdargs) if az0 <= fda))
                ji = findex[i + 1]
                embgg = embgammas[ji]

            z0 = act_flt_in_disc(embgg,CC(0),P)
            z0abs = z0.abs()
            if ji == -oldji:
                ji = next((j for j in range(-ngquats,0) + range(1,ngquats + 1) if j != -oldji and act_flt_in_disc(embgammas[j],z0,P).abs() < z0.abs),None)

            gg = gammas[ji]
            newcs = self.translate[ji]
            olddelta = delta
            delta = gg * delta
            oldji = ji
            tmp = newcs + self._get_word_recursive(delta,oldji,depth = depth + 1)
            return tmp

    def __magma_word_problem(self,x):
        r'''
        Given a quaternion x, finds its decomposition in terms of the generators

        INPUT: x can be a list/vector of integers (giving the quaternion in terms of the basis for the order,
        or x can be a quaternion, in which case the conversion is done in the function.

        OUTPUT: A list representing a word in the generators

        EXAMPLES:

        sage: G = ArithGroup(7,15,1)
        sage: G.__magma_word_problem(G.Ugens[2]*G.Ugens[1]) == [2,1]
        '''
        wtime = walltime()
        B = self.O
        x0 = x
        # If x is a quaternion, find the expression in the generators.
        if x.parent() is self.O or x.parent() is self.B:
            x = quaternion_to_magma_quaternion(self._B_magma,self.B(x))
        else:
            if len(x) != 4:
                raise ValueError, 'x (=%s) should be a list of length 4'%x
            x = quaternion_to_magma_quaternion(self._B_magma,self.B(sum(a*b for a,b in zip(self.Obasis,x))))
        x_magma = self._G_magma(x)
        #verbose('Calling _magma_word_problem with x = %s'%x)
        V = magma.WordProblem(x_magma).ElementToSequence()._sage_()
        delta1 = self.B(1)
        for v in V:
            delta1 = delta1 * self.Ugens[v - 1] if v > 0 else delta1 * self.Ugens[-v - 1]
        if delta1 != x0 and work_with_SL2:
            V.extend(self.minus_one_long)
        return V

    def element_of_norm(self,N,use_magma = False,return_all = False,radius = -1,max_elements = -1):
        N = ZZ(N)
        if return_all == False:
            try:
                return self._element_of_norm[N.gens_two()]
            except (AttributeError,KeyError):
                pass
        if not hasattr(self,'_element_of_norm'):
            self._element_of_norm  = dict([])

        if use_magma:
            assert return_all == False
            elt_magma = self._O_magma.ElementOfNorm(sage_F_ideal_to_magma(self._F_magma,N))
            candidate = self.B([magma_F_elt_to_sage(self.F,elt_magma.Vector()[m+1]) for m in range(4)])
            self._element_of_norm[N.gens_two()] = candidate
            return candidate
        else:
            v = list(self.Obasis)
            verbose('Doing long enumeration...')
            M = 0
            if return_all:
                all_candidates = []
            while M != radius:
                M += 1
                assert M < 9
                verbose('M = %s,radius = %s'%(M,radius))
                verbose('v = %s'%list(v))
                #for a0,an in product(range(M),product(range(-M,M+1),repeat = len(v)-1)):
                for an in product(range(-M,M+1), repeat = len(v)):
                    # candidate = sum((ZZ(ai) * vi for ai,vi in  zip([a0]+list(an),v)),self.B(0))
                    candidate = sum((ZZ(ai) * vi for ai,vi in  zip(an,v)),self.B(0))
                    # verbose('lincomb = %s'%([a0]+list(an)))
                    # verbose('candidate = %s'%candidate)
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
                raise RuntimeError,'Not found'

    @cached_method
    def get_hecke_reps(self,l,use_magma = False):
        r'''
        TESTS:

        sage: magma.eval('SetSeed(2000000)')
        sage: G = ArithGroup(6,5)
        sage: reps = G.get_hecke_reps(11)
        '''
        verbose('Finding hecke reps for l = %s'%l)
        g0 = self.element_of_norm(l,use_magma = use_magma)
        assert g0.reduced_norm() == l
        reps = [g0]
        ngens = len(self.gens())
        I = enumerate_words(range(ngens))
        n_iters = ZZ(0)
        num_reps = l + 1 if self.O.discriminant() % l !=0 else l
        while len(reps) < num_reps:
            n_iters += 1
            if n_iters % 50 == 0:
                verbose('%s, len = %s/%s'%(n_iters,len(reps),num_reps))
            v = I.next()
            new_candidate = prod([self.gen(i).quaternion_rep for i in v]) * g0
            new_inv = new_candidate**-1
            if not any([self._is_in_order(new_inv * old) for old in reps]):
                reps.append(new_candidate)
        return reps

    @cached_method
    def image_in_abelianized(self, x):
        r''' Given an element x in Gamma, returns its image in the abelianized group'''
        Gab,V,free_idx = self.abelianization()
        wd = x.word_rep
        tmp = Gab(sum(ZZ(a)*Gab(V.gen(g)) for g,a in wd))
        return (QQ**len(free_idx))([tmp[i] for i in free_idx])

    @cached_method
    def abelianization(self):
        V = ZZ**len(self.gens())
        W = V.span([sum(a*v for a,v in zip(V.gens(),rel)) for rel in self.get_relation_matrix().rows()])
        Gab = V/W
        free_idx = []
        for i in range(len(Gab.invariants())):
            if Gab.invariants()[i] == 0:
                free_idx.append(i)
        return Gab,V,free_idx


class ArithGroup_rationalmatrix(ArithGroup_generic):
    Element = Matrix
    def __init__(self,level,info_magma = None):
        self.F = QQ
        self.discriminant = ZZ(1)
        self.level = ZZ(level)

        self._prec_inf = -1

        self.__init_magma_objects(info_magma)
        self.B = MatrixSpace(QQ,2,2)
        self.Obasis = [matrix(ZZ,2,2,v) for v in [[1,0,0,0],[0,1,0,0],[0,0,self.level,0],[0,0,0,1]]]
        self.Ugens = [self.B([1,1,0,1]), self.B([1,0,level,1])]
        self._gens = [self.element_class(self,quaternion_rep = g, word_rep = [(i,1)],check = False) for i,g in enumerate(self.Ugens)]
        if self.level == 1:
            temp_relation_words = [6*[(0,-1),(1,1)],4*[(0,1),(1,-1),(0,1)]]
        else:
            temp_relation_words = [[(0,0)],[(1,0)]]
        self.minus_one = [(0,-1),(1,1),(0,-1),(1,1),(0,-1),(1,1)]

        self._relation_words = []
        for rel in temp_relation_words:
            sign = ZZ(prod((self._gens[g].quaternion_rep**a for g,a in rel), z = self.B(1)))
            if sign == 1:
                self._relation_words.append(rel)
            else:
                assert sign == -1
                if work_with_SL2:
                    newrel = rel + self.minus_one
                    sign = ZZ(prod((self._gens[g].quaternion_rep**a for g,a in newrel), z = self.B(1)))
                    assert sign == 1
                    self._relation_words.append(newrel)
                else:
                    self._relation_words.append(rel)

        self.GG = FreeGroup(len(self.gens())) / [syllables_to_tietze(rel) for rel in self.get_relation_words()]

        ArithGroup_generic.__init__(self)
        Parent.__init__(self)

    def _repr_(self):
        return 'Matrix Arithmetic Group of level = %s'%(self.level)

    def __init_magma_objects(self,info_magma = None):
        wtime = walltime()
        verbose('Calling _init_magma_objects...')
        if info_magma is None:
            ZZ_magma = magma.Integers()
            self._B_magma = magma.QuaternionAlgebra(magma.Rationals(),1,1)
            self._Omax_magma = self._B_magma.MaximalOrder()
            if self.level != ZZ(1):
                self._O_magma = self._Omax_magma.Order('%s'%self.level)
            else:
                self._O_magma = self._Omax_magma
        else:
            ZZ_magma = info_magma._B_magma.BaseRing().Integers()
            self._B_magma = info_magma._B_magma
            self._O_magma = info_magma._O_magma.Order('%s'%self.level)

        verbose('Spent %s seconds in init_magma_objects'%walltime(wtime))

    def _quaternion_to_list(self,x):
        a,b,c,d = x.list()
        return [a, b, QQ(c)/self.level, d]

    @cached_method
    def get_word_rep(self,delta):
        level = self.level
        if level != 1:
            raise ValueError,'Level (= %s)should be 1!'%self.level
        a,b,c,d = delta.list()
        m1 = matrix(ZZ,2,2,[1,0,0,1])
        tmp = []
        if c != 0:
            decomp = continued_fraction_list(QQ(a)/QQ(c))
            if len(decomp) % 2 == 1:
                decomp[-1] -= 1
                decomp.append(1)
            I = iter(decomp)
            for r,s in izip(I,I):
                tmp.extend([(0,r),(1,s)])
                m1 = m1 * matrix(ZZ,2,2,[1,r,0,1]) * matrix(ZZ,2,2,[1,0,s,1])
        T = m1**-1 * delta
        if not (( T[0,0] == 1 and T[1,1] == 1 and T[1,0] == 0) or ( T[0,0] == -1 and T[1,1] == -1 and T[1,0] == 0)):
            raise RuntimeError,'Entries of T (= %s) not correct'%T
        tmp.append((0,T[0,0]*T[0,1]))
        if T[0,0] == -1 and work_with_SL2:
            tmp.extend(self.minus_one)
        return tmp

    def element_of_norm(self,N,use_magma = False,local_condition = None):
        try:
            return self._element_of_norm[N]
        except (AttributeError,KeyError):
            pass
        if not hasattr(self,'_element_of_norm'):
            self._element_of_norm  = dict([])
        candidate = self.B([N,0,0,1])
        self._element_of_norm[N] = candidate
        return candidate

    @cached_method
    def get_hecke_reps(self,l,use_magma = False):
        r'''
        TESTS:

        sage: magma.eval('SetSeed(2000000)')
        sage: G = ArithGroup(6,5)
        sage: reps = G.get_hecke_reps(11)
        '''
        if use_magma:
            verbose("Warning: asked to use Magma to get hecke reps, but trivial to do without!")
        return [self.B([l,i,0,1]) for i in range(l)] + [self.B([1,0,0,l])]

    @cached_method
    def image_in_abelianized(self, x):
        r''' Given an element x in Gamma, returns its image in the abelianized group'''
        Gab,V,free_idx = self.abelianization()
        M = self.modsym_ambient
        f = self.modsym_map
        M1 = self.modsym_cuspidal
        a,b,c,d = x.quaternion_rep.list()
        tmp = Gab(M1.coordinate_vector(4*f(M([Cusps(Infinity),MatrixSpace(ZZ,2,2)(x.quaternion_rep) * Cusps(Infinity)]))))
        return (QQ**len(free_idx))([tmp[i] for i in free_idx])

    @cached_method
    def abelianization(self):
        self.modsym_ambient = ModularSymbols(self.level,sign = 1)
        self.modsym_cuspidal = self.modsym_ambient.cuspidal_subspace()[0]
        self.modsym_map = self.modsym_cuspidal.projection()
        ngens = self.modsym_cuspidal.dimension()
        V = ZZ**ngens
        W = V.span([])
        Gab = V/W
        free_idx = []
        for i in range(len(Gab.invariants())):
            if Gab.invariants()[i] == 0:
                free_idx.append(i)
        return Gab,V,free_idx


class FaceRel(SageObject):
    def __init__(self,center = None ,radius = None, mat = None):
        self.center = center
        self.radius = radius
        self.mat = mat

class ArithGroup_nf_quaternion(ArithGroup_generic):
    Element = ArithGroupElement
    def __init__(self,base,a,b,level,info_magma = None):
        self.F = base
        self.level = base.ideal(level)
        self.a,self.b = base(a),base(b)
        self.__init_magma_objects(info_magma)

        self.B = QuaternionAlgebra(self.F,self.a,self.b)

        magma_ZBasis = self._O_magma.ZBasis()
        tmpObasis = [magma_quaternion_to_sage(self.B,o) for o in magma_ZBasis]
        self.Obasis = tmpObasis
        Obasis = [[u for o in elt.coefficient_tuple() for u in o.list()] for elt in tmpObasis]
        self.basis_invmat = matrix(QQ,4*self.F.degree(),4*self.F.degree(),Obasis).transpose().inverse()

        self._O_discriminant = magma_F_ideal_to_sage(self.F,self._O_magma.Discriminant())
        verbose('Computing normalized basis')
        _,f,e = self._O_magma.NormalizedBasis(nvals = 3)
        verbose('Computing presentation')
        G,gens = f.Presentation(e,self._O_magma,nvals = 2)
        verbose('Done with presentation')
        self._init_aurel_data(f)
        Hm,GtoHm = magma.ReduceGenerators(G,nvals = 2)
        self._simplification_iso = []
        tmp_quaternions = []
        for i in range(len(gens)):
            self._simplification_iso.append(GtoHm.Image(G.gen(i+1)).ElementToSequence()._sage_())
            tmp_quaternions.append(magma_quaternion_to_sage(self.B,gens[i+1]))

        self.Ugens = []
        for h in Hm.gens():
            newgen = self.B(1)
            for i,ai in shorten_word(G(h).ElementToSequence()._sage_()):
                newgen = newgen * tmp_quaternions[i]**ai # FIXME
            self.Ugens.append(newgen)

        verbose('Initializing relations')
        if work_with_SL2:
            self.F_units = self.F.unit_group()
            self.F_unit_offset = len(self.Ugens)
            self.Ugens.extend([self.B(self.F(u)) for u in self.F_units.gens()])
            temp_relation_words = [shorten_word(Hm.Relations()[n+1].LHS().ElementToSequence()._sage_()) for n in range(len(Hm.Relations()))] + [[(self.F_unit_offset + i,u.multiplicative_order())] for i,u in enumerate(self.F_units.gens()) if u.multiplicative_order() != Infinity]
            self._relation_words = []
            for rel in temp_relation_words:
                remaining_unit = self.F_units(self.F(prod((self.Ugens[g]**a for g,a in rel), z = self.B(1))))
                assert remaining_unit.multiplicative_order() != Infinity
                ulist = remaining_unit.exponents()
                newrel = rel + [(self.F_unit_offset + i,a) for i,a in enumerate(ulist) if a != 0 ]
                sign = ZZ(prod((self.Ugens[g]**a for g,a in newrel), z = self.B(1)))
                assert sign == 1
                self._relation_words.append(newrel)

        else:
            self._relation_words = [shorten_word(Hm.Relations()[n+1].LHS().ElementToSequence()._sage_()) for n in range(len(Hm.Relations()))]

        self._gens = []
        for i,g in enumerate(self.Ugens):
            self._gens.append(ArithGroupElement(self,quaternion_rep = g, word_rep = [(i,1)],check = False))

        ArithGroup_generic.__init__(self)
        Parent.__init__(self)

    def _init_aurel_data(self,f):
        verbose('Initializing aurel_data')
        self._facerels_magma = f
        self._facerels = []
        self._RR = RR = RealField((len(str(f[1].Radius)) * RealField(20)(10).log()/RealField(20)(2).log()).ceil()-10)
        CC = ComplexField(RR.precision())
        vC = self.F.embeddings(CC)[0]
        tmp = magma.InfinitePlaces(self._F_magma)[1]
        if (vC(self.F.gen(0)).imag() * self._F_magma.gen(1).Evaluate(tmp).Im()._sage_()) < 0:
            vC = self.F.embeddings(CC)[1]
            assert (vC(self.F.gen(0)).imag() * self._F_magma.gen(1).Evaluate(tmp).Im()._sage_()) > 0
        self._vC = vC
        self._HH = QuaternionAlgebra(RR,-1,-1)
        ih,jh,kh = self._HH.gens()
        self._Pmat, self._Pmatinv = JtoP(self._HH,MatrixSpace(CC,2,2))
        matlist = magma.GetMatrixList(f)
        i,j,k  = self.B.gens()
        for idx in range(len(f)):
            frel_m = f[idx+1]
            center = self._HH(sage_eval(str(frel_m.Center),{'i' : ih,'j' : jh}))
            radius = RR(sage_eval(str(frel_m.Radius)))
            mat = Matrix(self._HH,2,2,sage_eval(str(matlist[idx+1]),{'i' : ih, 'j': jh, 'k': kh}))
            self._facerels.append(FaceRel(center,radius,mat))
        verbose('Done with init_aurel_data')

    def _repr_(self):
        return 'Arithmetic Group attached to quaternion algebra with a = %s, b = %s and level = %s'%(self.a,self.b,self.level)

    def __init_magma_objects(self,info_magma = None):
        wtime = walltime()
        verbose('Calling _init_magma_objects...')
        if info_magma is None:
            Qx_magma = magma.PolynomialRing(magma.Rationals())
            xm = Qx_magma.gen(1)
            f = self.F.gen().minpoly()
            fmagma = sum([magma(c)*xm**i for c,i in zip(f.coefficients(),f.exponents())])
            FF_magma = magma.NumberField(fmagma)
            self._F_magma = FF_magma
            OF_magma = FF_magma.Integers()
            am, bm = sage_F_elt_to_magma(self._F_magma,self.a),sage_F_elt_to_magma(self._F_magma,self.b)
            self._B_magma = magma.QuaternionAlgebra(FF_magma,am,bm)

            self._Omax_magma = self._B_magma.MaximalOrder()
            if self.level != self.F.ideal(1):
                self._O_magma = self._Omax_magma.Order(sage_F_ideal_to_magma(self._F_magma,self.level))
            else:
                self._O_magma = self._Omax_magma

        else:
            self._F_magma = info_magma._F_magma
            OF_magma = info_magma._F_magma.Integers()
            self._B_magma = info_magma._B_magma
            self._Omax_magma = info_magma._B_magma.MaximalOrder()
            if self.level != self.F.ideal(1):
                self._O_magma = self._Omax_magma.Order(sage_F_ideal_to_magma(self._F_magma,self.level))
            else:
                self._O_magma = self._Omax_magma

        verbose('Spent %s seconds in init_magma_objects'%walltime(wtime))

    def _quaternion_to_list(self,x):
        xlist = [u for o in x.coefficient_tuple() for u in o.list()]
        return (self.basis_invmat * matrix(QQ,4 * self.F.degree() ,1,xlist)).list()

    @cached_method
    def get_word_rep(self,gamma):
        # if not self._is_in_order(gamma):
        #     raise RuntimeError,'gamma (= %s) is not in order!'%gamma
        HH = self._HH
        R = HH.base_ring()
        boundary = self._facerels
        eps = 2**-(R(HH.base_ring().precision())/R(2))
        #verbose('eps = %s'%eps)
        z = HH(0)
        mat_gamma = self._kleinianmatrix(gamma**-1)
        gammaz = act_H3(mat_gamma,z)
        if len(boundary) == 0:
            raise RuntimeError, 'Empty boundary'
        B = self.B
        deltaword = []
        lengthw = 0
        delta = B(1)
        while True:
            d = R(1)
            i0 = None
            #verbose('gammaz = %s'%gammaz)
            for i,b in enumerate(boundary):
                d1 = sum((o**2 for o in (gammaz - b.center).coefficient_tuple()))/b.radius**2
                if d >= (1+eps)*d1:
                    d = d1
                    i0 = i
                    # break # This might yield longer words, but should be faster!
            if i0 is None:
                break
            gammaz = act_H3(boundary[i0].mat,gammaz)
            deltaword.append(i0+1)
            #verbose('deltaword = %s'%deltaword)
            lengthw += 1
        deltaword.reverse()
        c = sum((list(self._simplification_iso[o-1]) for o in deltaword),[])
        tmp = [(g-1,len(list(a))) if g > 0 else (-g-1,-len(list(a))) for g,a in groupby(c)]
        return reduce_word(tmp)

    @cached_method
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

    def _is_in_order(self,x):
        return all([o.is_integral() for o in self._quaternion_to_list(x)])

    def enumerate_elements(self,max_length = None):
        if work_with_SL2:
            ngens = self.F_unit_offset
        else:
            ngens = len(self.gens())
        for v in enumerate_words(range(ngens)):
            if max_length is not None and len(v) > max_length:
                raise StopIteration
            else:
                yield prod([self.Ugens[i] for i in v])

    def compute_quadratic_embedding(self,K,return_generator = False):
        O_magma = self._O_magma
        F_magma = self._F_magma

        assert K.base_field() == self.F
        Fxmagma = magma.PolynomialRing(F_magma)
        Fxmagma.assign_names('x')
        xm = Fxmagma.gen(1)
        b = K.gen()
        f = b.minpoly()
        fm = sum([sage_F_elt_to_magma(self._F_magma,c) * xm**i for c,i in zip(f.coefficients(),f.exponents())])
        K_magma = magma.NumberField(fm)
        OK_magma = K_magma.MaximalOrder()
        verbose('Calling magma Embed function...')
        try:
            _,iota = magma.Embed(OK_magma,O_magma,nvals = 2)
        except RuntimeError:
            print 'An error ocurred!'
            print 'OK_magma = ',OK_magma
            print 'O_magma =',O_magma
            raise RuntimeError
        verbose('Calling magma Embed function done!')
        wm = K_magma(OK_magma.Basis()[2])
        w = K(magma_F_elt_to_sage(self.F,wm[1]) + magma_F_elt_to_sage(self.F,wm[2]) * b)
        ans = magma_integral_quaternion_to_sage(self.B,O_magma,F_magma,iota.Image(OK_magma(K_magma.gen(1))))
        assert ans.reduced_norm() == K.gen().norm(self.F) and ans.reduced_trace() == K.gen().trace(self.F)
        ans = self.B(ans)
        if return_generator:
            verbose('w = %s, minpoly = %s'%(w,w.minpoly()))
            assert w in K.maximal_order()
            return ans,w
        else:
            return ans

    def embed_order(self,p,K,prec,zero_deg = True,outfile = None,return_all = False):
        r'''
        '''
        verbose('Computing quadratic embedding to precision %s'%prec)
        mu = self.compute_quadratic_embedding(K,return_generator = False)
        verbose('Finding module generators')
        w = module_generators(K)[1]
        verbose('Done')
        w_minpoly = PolynomialRing(Qp(p,prec),names = 'x')([self._F_to_Qp(o) for o in w.minpoly().coeffs()])
        verbose('w_minpoly = %s'%w_minpoly)
        Cp = Qp(p,prec).extension(w_minpoly,names = 'g')
        verbose('Cp is %s'%Cp)
        wl = w.list()
        assert len(wl) == 2
        r0 = -wl[0]/wl[1]
        r1 = 1/wl[1]
        assert r0+r1*w == K.gen()
        padic_Kgen = Cp(self._F_to_Qp(r0))+Cp(self._F_to_Qp(r1))*Cp.gen()
        try:
            fwrite('d_K = %s, h_K = %s, h_K^- = %s'%(K.discriminant(),K.class_number(),len(K.narrow_class_group())),outfile)
        except NotImplementedError: pass
        fwrite('w_K satisfies: %s'%w.minpoly(),outfile)
        assert K.gen(0).trace(K.base_ring()) == mu.reduced_trace() and K.gen(0).norm(K.base_ring()) == mu.reduced_norm()

        iotap = self.get_embedding(prec)
        fwrite('Local embedding B to M_2(Q_p) sends i to %s and j to %s'%(iotap(self.B.gens()[0]).change_ring(Qp(p,5)).list(),iotap(self.B.gens()[1]).change_ring(Qp(p,5)).list()),outfile)
        a,b,c,d = iotap(mu).list()
        X = PolynomialRing(Cp,names = 'X').gen()
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
        fwrite('\cO_K to R_0 given by w_K |-> %s'%mu,outfile)
        fwrite('gamma_psi = %s'%gamma,outfile)
        fwrite('tau_psi = %s'%tau1,outfile)
        fwrite('(where g satisfies: %s)'%w.minpoly(),outfile)
        if return_all:
            return gamma, tau1, tau2
        else:
            return gamma, tau1

    def element_of_norm(self,N,use_magma = False,return_all = False,radius = -1,max_elements = -1):
        N = self.F.ideal(N)
        if return_all == False:
            try:
                return self._element_of_norm[N.gens_two()]
            except (AttributeError,KeyError):
                pass
        else:
            if radius < 0 and max_elements < 0:
                raise ValueError,'Radius must be positive'

        if not hasattr(self,'_element_of_norm'):
            self._element_of_norm  = dict([])

        if use_magma:
            assert return_all == False
            elt_magma = self._O_magma.ElementOfNorm(sage_F_ideal_to_magma(self._F_magma,N))
            elt_magma_vector = elt_magma.Vector()
            candidate = self.B([magma_F_elt_to_sage(self.F,elt_magma_vector[m+1]) for m in range(4)])
            self._element_of_norm[N.gens_two()] = candidate
            return candidate
        else:
            v = self.Obasis
            verbose('Doing long enumeration...')
            M = 0
            if return_all:
                all_candidates = []
            while M != radius:
                M += 1
                verbose('M = %s,radius = %s'%(M,radius))
                for a0,an in product(range(M),product(range(-M+1,M),repeat = len(v)-1)):
                    candidate = self.B(sum(ai*vi for ai,vi in  zip([a0]+list(an),v)))
                    if self.F.ideal(candidate.reduced_norm()) == N:
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
                raise RuntimeError,'Not found'

    @cached_method
    def get_hecke_reps(self,l,use_magma = False):
        r'''
        TESTS:

        sage: magma.eval('SetSeed(2000000)')
        sage: G = ArithGroup(6,5)
        sage: reps = G.get_hecke_reps(11)
        '''
        l = self.F.ideal(l)
        g0 = self.element_of_norm(l,use_magma = use_magma)
        reps = [g0]
        I = self.enumerate_elements()
        n_iters = ZZ(0)
        num_reps = l.norm() if l.divides(self._O_discriminant) else l.norm() + 1
        while len(reps) < num_reps:
            n_iters += 1
            if n_iters % 50 == 0:
                verbose('%s, len = %s/%s'%(n_iters,len(reps),num_reps))
            new_candidate = I.next() * g0
            new_inv = new_candidate**-1
            if not any([self._is_in_order(new_inv * old) for old in reps]):
                reps.append(new_candidate)
        return reps

    @cached_method
    def image_in_abelianized(self, x):
        r''' Given an element x in Gamma, returns its image in the abelianized group'''
        Gab,V,free_idx = self.abelianization()
        wd = x.word_rep
        tmp = Gab(sum(ZZ(a)*Gab(V.gen(g)) for g,a in wd))
        return (QQ**len(free_idx))([tmp[i] for i in free_idx])

    @cached_method
    def abelianization(self):
        # print 'Warning!! Loading W.sobj from disk, could be anything!'
        # return load('abelianized.sobj')
        V = ZZ**len(self.gens())
        W = V.span([sum(a*v for a,v in zip(V.gens(),rel)) for rel in self.get_relation_matrix().rows()])
        Gab = V/W
        free_idx = []
        for i in range(len(Gab.invariants())):
            if Gab.invariants()[i] == 0:
                free_idx.append(i)
        return Gab,V,free_idx
