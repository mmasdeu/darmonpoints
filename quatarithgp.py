######################
##                  ##
##    QUATERNIONIC  ##
##    ARITHMETIC    ##
##    GROUP         ##
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
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,NumberField,lcm
from sage.rings.padics.all import Qp
from sage.functions.trig import arctan
from sage.interfaces.magma import magma
from sage.all import prod
from collections import defaultdict
from itertools import product,chain,izip,groupby,islice,tee,starmap
from sigma0 import Sigma0,Sigma0ActionAdjuster
from util import *
from homology import Divisors, Homology
from sage.structure.sage_object import save,load
from copy import copy
from sage.misc.persist import db

def load_bigarithgroup(fname):
    G = load(fname)
    G._restore_magma_objects()
    return G

class BTEdge(SageObject):
    r'''
    A BTEdge is represented by an element `gamma`, and then a flag called `reverse`.
    The flag reverse indicates whether we refer to the opposite edge of the one
    represented by `gamma`.
    '''
    def __init__(self,reverse,gamma):
        self.reverse = reverse
        self.gamma = gamma

    def _repr_(self):
        return "(%s)^%s"%(self.gamma,'+' if self.reverse == False else '-')

    def __iter__(self):
        return iter([self.reverse,self.gamma])

def BigArithGroup(p,discriminant,level,seed = None,use_sage_db = True,outfile = None):
        if seed is None:
            seed = 1000000
        fname = 'arithgroup%s_%s_%s_%s.sobj'%(seed,p,discriminant,level)
        if use_sage_db:
            try:
                newobj = db(fname)
                newobj._restore_magma_objects()
            except IOError:
                newobj = BigArithGroup_class(p,discriminant,level,seed,outfile = outfile)
                newobj.save_to_db()
        else:
            newobj = BigArithGroup_class(p,discriminant,level,seed,outfile = outfile)
        return newobj

class BigArithGroup_class(AlgebraicGroup):
    r'''
    This class hold information about the group `\Gamma`: a finite
    presentation for it, a solution to the word problem,...

    Initializes the group attached to a `\ZZ[1/p]`-order of the rational quaternion algebra of
    discriminant `discriminant` and  level `n`.

    TESTS:

        sage: G = BigArithGroup(7,15,1)
        sage: a = G([(1,2),(0,3),(2,-1)])
        sage: b = G([(1,3)])
        sage: c = G([(2,1)])
        sage: print a*b
        Element in Arithmetic Group attached to data p = 7, disc = 15, level = 1
        Word representation: [(1, 2), (0, 3), (2, -1), (1, 3)]
        sage: a.quaternion_rep
        618 + 787/4*i - 239*j - 787/4*k
        sage: b.quaternion_rep
        -1
        sage: print a*b
        Element in Arithmetic Group attached to data p = 7, disc = 15, level = 1
        Quaternion representation: -618 - 787/4*i + 239*j + 787/4*k
        Word representation: [(1, 2), (0, 3), (2, -1), (1, 3)]
        sage: x = G((a*b).quaternion_rep)
        sage: x.word_rep
        [(1, -1), (0, 3), (2, -1)]
        sage: (a*b).word_rep
        [(1, 2), (0, 3), (2, -1), (1, 3)]
    '''
    def __init__(self,p,discriminant,level,seed,outfile = None):
        self.seed = seed
        verbose('Setting Magma seed to %s'%seed)
        magma.eval('SetSeed(%s)'%seed)
        self.p = ZZ(p)
        if not self.p.is_prime():
            raise ValueError, 'p ( = %s) must be prime'%self.p
        if isinstance(discriminant,list):
            tmp = QuaternionAlgebra(discriminant[0],discriminant[1])
            disc = tmp.discriminant()
            self.discriminant = ZZ(tmp.discriminant())
        else:
            self.discriminant = ZZ(discriminant)
        self.level = ZZ(level)
        if len(self.discriminant.factor()) % 2 != 0:
            raise ValueError, 'Discriminant must contain an even number of primes'
        verbose('Initializing arithmetic group G(n)...')
        self.Gn = ArithGroup(discriminant,level)
        self.Gn.get_embedding = self.get_embedding
        self.Gn.embed = self.embed
        verbose('Initializing arithmetic group G(pn)...')
        self.Gpn = ArithGroup(discriminant,p*level,info_magma = self.Gn)
        fwrite('B = Q<i,j,k>, with i^2 = %s and j^2 = %s'%(self.Gn.B.gens()[0]**2,self.Gn.B.gens()[1]**2),outfile)
        fwrite('R with basis %s'%list(self.Gn.Obasis),outfile)
        fwrite('R(p) with basis %s'%list(self.Gpn.Obasis),outfile)
        self.Gpn.get_embedding = self.get_embedding
        self.Gpn.embed = self.embed
        self._prec = -1
        # self._II_exact,self._JJ_exact,self._KK_exact = self._compute_exact_quadratic_splitting()

        self.get_Up_reps()
        verbose('Done initializing arithmetic groups')
        self.Gpn.get_Up_reps = self.get_Up_reps

        del self.Gpn._m2_magma
        del self.Gn._m2_magma
        del self.Gpn._U_magma
        del self.Gn._U_magma
        del self.Gpn._D_magma
        del self.Gn._D_magma
        del self.Gpn._G_magma
        del self.Gn._G_magma

        verbose('Done initialization of BigArithmeticGroup')

    def _repr_(self):
        return 'Big Arithmetic Group attached to data p = %s,  disc = %s, level = %s'%(self.p,self.discriminant,self.level)

    def _restore_magma_objects(self):
        a,b = self.Gn.B.invariants()
        QQmagma = magma.RationalsAsNumberField()
        ZZ_magma = QQmagma.Integers()
        B_magma = magma.QuaternionAlgebra(QQmagma,a,b)
        self.Gn._B_magma = B_magma
        self.Gpn._B_magma = B_magma
        self.Gn._Omax_magma = B_magma.MaximalOrder()
        self.Gpn._Omax_magma = B_magma.MaximalOrder()
        if self.discriminant != 1:
            self.Gn._O_magma = self.Gn._Omax_magma.Order('%s*%s'%(self.Gn.level,ZZ_magma.name()))
            self.Gpn._O_magma = self.Gn._Omax_magma.Order('%s*%s'%(self.Gpn.level,ZZ_magma.name()))
        else:
            self.Gn._O_magma = self.Gn._Omax_magma.Order('%s'%self.Gn.level)
            self.Gpn._O_magma = self.Gn._Omax_magma.Order('%s'%self.Gpn.level)

    def _compute_exact_quadratic_splitting(self):
        # Now we compute a splitting
        Btmp = magma.QuaternionAlgebra(magma.Rationals(),self.Gn.B.invariants()[0],self.Gn.B.invariants()[1])
        def quat_to_mquat(x):
            v = list(x)
            return Btmp(v[0]) + sum(v[i+1]*Btmp.gen(i+1) for i in range(3))
        R = magma.QuaternionOrder([quat_to_mquat(o) for o in self.Gpn.Obasis])
        if self.p <= 3:
            disc = 7
        elif kronecker_symbol(2,self.p) == 1:
            disc = 2
        elif kronecker_symbol(3,self.p) == 1:
            disc = 3
        else:
            disc = 6
        assert kronecker_symbol(disc,self.p) == 1
        self._splitting_field = QuadraticField(disc,names = 'a')
        Fmagma = magma.QuadraticField(disc)
        g = Fmagma.Embed(Btmp)
        # FIXME
        f = R.MatrixRepresentation(nvals = 1)
        self._splitting_field = NumberField(f.Codomain().BaseRing().DefiningPolynomial().sage(),names = 'a')
        allmats = []
        for kk in range(4):
           x = magma.eval('x:=%s(%s)'%(f.name(),R.gen(kk+1).name()))#f.Image(self._O_magma.gen(kk+1))
           all_str=[]
           for ii in range(2):
               for jj in range(2):
                   magma.eval('v%s%s:=[Sage(z) : z in Eltseq(x[%s,%s])]'%(ii,jj,ii+1,jj+1))
           v=[self._splitting_field(magma.eval('Sprint(v%s)'%tt)) for tt in ['00','01','10','11']]
           allmats.append(Matrix(self._splitting_field,2,2,v))
        ansmats = []
        for col in self.Gpn.basis_invmat.columns()[1:]:
            ansmats.append(sum(a*b for a,b in zip(allmats,col.list())))
        return ansmats

    def _local_splitting(self,prec):
        r"""
        Finds an embedding of the definite quaternion algebra
        into the algebra of 2x2 matrices with coefficients in `\QQ_p`.

        INPUT:

        - prec -- Integer. The precision of the splitting.

        OUTPUT:

        - Matrices I, J, K giving the splitting.

        EXAMPLES::

            sage: X = BigArithGroup(13,2*3,1)
            sage: phi = X._local_splitting(10)
            sage: B.<i,j,k> = QuaternionAlgebra(3)
            sage: phi(i)**2 == QQ(i**2)*phi(B(1))
            True

        """
        prime = self.p
        if prec <= self._prec:
            return self._II,self._JJ,self._KK

        # F = self._II_exact.base_ring()
        # QQp = Qp(prime,prec)
        # alphap = our_sqrt(QQp(F.gen()**2),QQp)
        # phi = F.hom([alphap])
        # self._II = self._II_exact.apply_morphism(phi)
        # self._JJ = self._JJ_exact.apply_morphism(phi)
        # self._KK = self._KK_exact.apply_morphism(phi)
        magma.eval('SetSeed(%s)'%self.seed)
        M,f,_ = magma.pMatrixRing(self.Gn._Omax_magma.name(),prime*self.Gn._Omax_magma.BaseRing(),nvals = 3)
        QQp = Qp(prime,prec)
        self._prec = prec
        B_magma = self.Gn._B_magma
        v = f.Image(B_magma.gen(1)).Vector()
        self._II = matrix(QQp,2,2,[v[i+1]._sage_() for i in range(4)])
        v = f.Image(B_magma.gen(2)).Vector()
        self._JJ = matrix(QQp,2,2,[v[i+1]._sage_() for i in range(4)])
        v = f.Image(B_magma.gen(3)).Vector()
        self._KK = matrix(QQp,2,2,[v[i+1]._sage_() for i in range(4)])
        # Test splitting
        for g in self.Gpn.Obasis:
            tup = g.coefficient_tuple()
            mat = tup[0] + tup[1]*self._II + tup[2]*self._JJ + tup[3]*self._KK
            assert is_in_Gamma0loc(mat,det_condition = False)
        return self._II, self._JJ, self._KK

    def save_to_db(self):#,fname):
        fname = 'arithgroup%s_%s_%s_%s.sobj'%(self.seed,self.p,self.discriminant,self.level)
        B_magma = self.Gn._B_magma
        Omax_magma = self.Gn._Omax_magma
        O1_magma = self.Gn._O_magma
        O2_magma = self.Gpn._O_magma
        del self.Gn._Omax_magma
        del self.Gn._O_magma
        del self.Gn._B_magma
        del self.Gpn._Omax_magma
        del self.Gpn._O_magma
        del self.Gpn._B_magma
        self.db(fname)
        self.Gn._B_magma = B_magma
        self.Gpn._B_magma = B_magma
        self.Gn._Omax_magma = Omax_magma
        self.Gpn._Omax_magma = Omax_magma
        self.Gn._O_magma = O1_magma
        self.Gpn._O_magma = O2_magma

    def small_group(self):
        return self.Gpn

    def small_group_gens(self):
        return self.Gpn.gens()


    @cached_method
    def get_BT_reps(self):
        reps = [self.Gn.B(1)] + [None for i in range(self.p)]
        emb = self.get_embedding(20)
        wp = self.wp
        matrices = [(i+1,matrix(QQ,2,2,[i,1,-1,0])) for i in range(self.p)]
        for n_iters,elt0 in enumerate(self.Gn.enumerate_elements()):
            elt = elt0.quaternion_rep
            new_inv = elt**(-1)
            for idx,o1 in enumerate(matrices):
                i,mat = o1
                tmp = emb(elt) * mat
                if all([not self.Gpn._is_in_order(o * new_inv) for o in reps if o is not None]) and is_in_Gamma0loc(tmp) and (emb(elt)[0,0]-1).valuation() > 0:
                    reps[i] = set_immutable(elt)
                    del matrices[idx]
                    verbose('%s, len = %s/%s'%(n_iters,self.p+1-len(matrices),self.p+1))
                    if len(matrices) == 0:
                        return reps
                    break

    def do_tilde(self,g):
        return QQ(-1)/QQ(self.p) * self.wp * g * self.wp

    @cached_method
    def get_BT_reps_twisted(self):
        return [self.Gn.B(1)] + [self.do_tilde(g) for g in self.get_BT_reps()[1:]]

    @cached_method
    def get_Up_reps(self):
        if self.level % self.p == 0:
            raise NotImplementedError
        tmp = [-self.p * o**-1 * self.wp**-1 for o in self.get_BT_reps()[1:]] # note the -1 in wp!
        return tmp

    def get_covering(self,depth):
        return self.subdivide([BTEdge(False, o) for o in self.get_BT_reps_twisted()], 1, depth - 1)

    def subdivide(self,edgelist,parity,depth):
        if depth < 0:
            return []
        if depth == 0:
            for rev,gamma in edgelist:
                set_immutable(gamma)
                return edgelist
        newEgood = []
        for rev,gamma in edgelist:
            if parity % 2 == 0:
                newEgood.extend([BTEdge(not rev, e * gamma) for e in self.get_BT_reps_twisted()[1:]])
            else:
                newEgood.extend([BTEdge(not rev, e * gamma) for e in self.get_BT_reps()[1:]])
        return self.subdivide(newEgood,1-parity,depth - 1)

    @lazy_attribute
    def wp(self):
        verbose('Finding a suitable wp...')
        if self.discriminant == 1:
            return matrix(QQ,2,2,[0,-1,self.p,0])
        else:
            epsinv = matrix(QQ,2,2,[0,-1,self.p,0])**-1
            tmp = self.Gpn.element_of_norm(self.p)
            for v1,v2 in cantor_diagonal(self.Gn.enumerate_elements(),self.Gn.enumerate_elements()):
                new_candidate =   v2.quaternion_rep * tmp *  v1.quaternion_rep
                if is_in_Gamma0loc(epsinv * self.embed(new_candidate,20), det_condition = False) and all([self.Gpn._is_in_order(new_candidate**-1 * g * new_candidate) for g in self.Gpn.Obasis]):
                        return new_candidate

    def get_embedding(self,prec):
        r"""
        Returns an embedding of the quaternion algebra
        into the algebra of 2x2 matrices with coefficients in `\QQ_p`.

        INPUT:

        - prec -- Integer. The precision of the splitting.

        """
        if self.discriminant != 1:
            I,J,K = self._local_splitting(prec)
            def iota(q):
                R=I.parent()
                v = q
                try:
                    v = v.coefficient_tuple()
                except AttributeError: pass
                return R(v[0] + I*v[1] + J*v[2] + K*v[3])
        else:
            R =  Qp(self.p,prec)
            def iota(q):
                #return q.apply_map(lambda x:R(x))
                return q.change_ring(R)
        return iota

    def embed(self,q,prec):
        if self.discriminant != 1:
            I,J,K = self._local_splitting(prec)
            R=I.parent()
            v = q
            try:
                v = v.coefficient_tuple()
            except AttributeError: pass
            return R(v[0] + I*v[1] + J*v[2] + K*v[3])
        else:
            return q.change_ring(Qp(self.p,prec))

    def reduce_in_amalgam(self,x,return_word = False):
        rednrm = x.reduced_norm() if self.discriminant != 1 else x.determinant()
        if rednrm != 1:
            raise ValueError,'x (= %s) must have reduced norm 1'%x
        a,wd = self._reduce_in_amalgam(set_immutable(x))
        if return_word == True:
            return a,wd
        else:
            return a


    @cached_method
    def _reduce_in_amalgam(self,x):
        x0 = x
        p = self.p
        rednrm = x.reduced_norm() if self.discriminant != 1 else x.determinant()
        denval = self.Gn._denominator_valuation
        x = set_immutable(p**-ZZ(QQ(rednrm.valuation(p))/QQ(2)) * x)
        if self.Gpn._denominator(x) == 1:
            return x,[]
        else:
            gis = [ g**-1 for g in self.get_BT_reps()]
            gitildes = [self.Gn.B(1)] + [ g**-1 for g in self.get_BT_reps_twisted()[1:]]

            xtilde = self.do_tilde(x)
            valx = denval(xtilde,p)
            if valx == 0:
                valx = 1
            found = False

            i = next((i for i,g in enumerate(gitildes) if denval(xtilde * g,p) < valx),0)
            wd0 = (i,0)
            x = x * gis[i]

            valx = denval(x,p)
            if valx == 0:
                valx = 1

            if self.Gpn._denominator(x) == 1:
                return x, [wd0]

            i = next((i for i,g in enumerate(gitildes) if denval(x * g,p) < valx),0)
            assert i > 0
            wd1 = (i,1)
            x = set_immutable(x * gitildes[i])
            a,wd = self._reduce_in_amalgam(x)
            return a, wd + [wd1,wd0]

    def construct_cycle(self,D,prec,hecke_smoothen = True,outfile = None):
        gamma, tau = self.Gn.embed_order(self.p,D,prec,outfile = outfile)
        Div = Divisors(tau.parent())
        D1 = Div(tau)
        H1 = Homology(self.Gn,Div)
        gamman = gamma
        found = False
        n = 1
        while not found:
            try:
                tmp = H1(dict([(gamman,D1)])).zero_degree_equivalent()
                found = True
            except ValueError:
                n += 1
                gamman *= gamma
        if hecke_smoothen:
            q = ZZ(2)
            D = self.Gpn.O.discriminant()
            while D%q == 0:
                q = q.next_prime()
            tmp = tmp.hecke_smoothen(q,prec = prec)#.factor_into_generators()
        return tmp,n,q

class ArithGroup(AlgebraicGroup):
    def __init__(self,discriminant,level,info_magma = None):
        if isinstance(discriminant,list):
            tmp = QuaternionAlgebra(discriminant[0],discriminant[1])
            self.abtuple = discriminant
            self.discriminant = ZZ(tmp.discriminant())
        else:
            self.discriminant = ZZ(discriminant)
        self.level = ZZ(level)

        self._prec_inf = -1

        if len(self.discriminant.factor()) % 2 != 0:
            raise ValueError, 'Discriminant must contain an even number of primes'

        self._init_magma_objects(info_magma)
        if self.discriminant != 1:
            self.B = QuaternionAlgebra((self._B_magma.gen(1)**2)._sage_(),(self._B_magma.gen(2)**2)._sage_())
            if self.B.discriminant() != self.discriminant:
                print 'Error while constructing quaternion algebra...'
                assert 0
            self.O = self.B.quaternion_order([self.B([QQ(self._O_magma.ZBasis()[n+1].Vector()[m+1]) for m in range(4)]) for n in range(4)])
            self.Obasis = self.O.basis()
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
            emb = self.get_archimedean_embedding(200)
            self.gquats = translate_into_twosided_list([[self.B([self._B_magma(gquats_magma[i+1][n+1].Quaternion()).Vector()[m+1] for m in range(4)]) for n in range(len(gquats_magma[i+1]))] for i in range(2)])
            self.embgquats =  [None] + [emb(g) for g in self.gquats[1:]]

            self.pi = RealField(100)(4)*arctan(1)
            self.findex = [ZZ(x._sage_()) for x in self._G_magma.get_magma_attribute('ShimGroupSidepairsIndex')]
            self.fdargs = [RealField(200)(x._sage_()) for x in self._G_magma.get_magma_attribute('ShimFDArgs')]

            self.minus_one_long = [ len(self.Ugens) + 1 ]
            self.minus_one = shorten_word(self.minus_one_long)
            self.Ugens.append(self.B(-1))

            self.translate = [None] + [self._magma_word_problem(g**-1) for g in self.gquats[1:]]

            self._gens = [ ArithGroupElement(self,quaternion_rep = g, word_rep = [(i,1)],check = False) for i,g in enumerate(self.Ugens) ]

            temp_relation_words = [shorten_word(self._U_magma.Relations()[n+1].LHS().ElementToSequence()._sage_()) for n in range(len(self._U_magma.Relations()))] + [[(len(self.Ugens)-1,2)]]
        else:
            self.B = MatrixSpace(QQ,2,2)
            self.Obasis = [matrix(ZZ,2,2,v) for v in [[1,0,0,0],[0,1,0,0],[0,0,self.level,0],[0,0,0,1]]]
            self.Ugens = [self.B([1,1,0,1]), self.B([1,0,level,1])]
            self._gens = [ArithGroupElement(self,quaternion_rep = g, word_rep = [(i,1)],check = False) for i,g in enumerate(self.Ugens)]
            if self.level == 1:
                temp_relation_words = [6*[(0,-1),(1,1)],4*[(0,1),(1,-1),(0,1)]]
            else:
                temp_relation_words = [[(0,0)],[(1,0)]]
            self.minus_one = [(0,-1),(1,1),(0,-1),(1,1),(0,-1),(1,1)]

        self._relation_words = []
        for rel in temp_relation_words:
            sign = prod((self._gens[g].quaternion_rep**a for g,a in rel), z = self.B(1))
            if sign == 1:
                self._relation_words.append(rel)
            elif sign == -1:
                newrel = rel + self.minus_one
                sign = prod((self._gens[g].quaternion_rep**a for g,a in newrel), z = self.B(1))
                assert sign == 1
                #self._relation_words.append(reduce_word(2*rel))
                self._relation_words.append(newrel)
            else:
                print 'What? Sign should be either +1 or -1!'
                assert 0
        # Define the (abelian) relation matrix
        self._relation_matrix = matrix(ZZ,len(self._relation_words),len(self._gens),0)
        for i,rel in enumerate(self._relation_words):
            for j,k in rel:
                self._relation_matrix[i,j] += k
        Parent.__init__(self)

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

    def _repr_(self):
        return 'Arithmetic Group attached to data  disc = %s, level = %s'%(self.discriminant,self.level)

    def one(self):
        return ArithGroupElement(self,word_rep = [])

    def _element_constructor_(self,x):
        if isinstance(x,list):
            return ArithGroupElement(self, word_rep = x)
        elif x.parent() is self.quaternion_algebra():
            return ArithGroupElement(self, quaternion_rep = x)
        elif isinstance(x.parent(),sage.modules.free_module.FreeModule_generic):
            Ga, V, free_idx = self.abelianization()
            indices_vec = [Ga.gen(o).lift() for o in free_idx]
            return ArithGroupElement(self,word_rep = [(idx,n) for indices in indices_vec for idx,n in zip(indices,x)])
        else:
            return ArithGroupElement(self, quaternion_rep = x)

    def _coerce_map_from_(self,S):
        r"""
        The only things that coerce into this group are:
        - lists
        - elements in the quaternion algebra, of reduced norm 1
        """
        if isinstance(S,list):
            return True
        return False
 
    def _init_magma_objects(self,info_magma = None):
        wtime = walltime()
        verbose('Calling _init_magma_objects...')
        if info_magma is None:
            if self.discriminant != 1:
                QQ_magma = magma.RationalsAsNumberField()
                ZZ_magma = QQ_magma.Integers()
                if hasattr(self,'abtuple'):
                    self._B_magma = magma.QuaternionAlgebra('%s'%QQ_magma.name(),self.abtuple[0],self.abtuple[1])
                else:
                    self._B_magma = magma.QuaternionAlgebra('%s*%s'%(self.discriminant,ZZ_magma.name()))

                self._Omax_magma = self._B_magma.MaximalOrder()
                self._O_magma = self._Omax_magma.Order('%s*%s'%(self.level,ZZ_magma.name()))
                self._D_magma = magma.UnitDisc(Precision = 300)
            else:
                ZZ_magma = magma.Integers()
                self._B_magma = magma.QuaternionAlgebra(magma.Rationals(),1,1)
                self._Omax_magma = self._B_magma.MaximalOrder()
                self._O_magma = self._Omax_magma.Order('%s'%self.level)
        else:
            ZZ_magma = info_magma._B_magma.BaseRing().Integers()
            self._B_magma = info_magma._B_magma
            if self.discriminant != 1:
                self._Omax_magma = info_magma._B_magma.MaximalOrder()
                self._O_magma = self._Omax_magma.Order('%s*%s'%(self.level,ZZ_magma.name()))
                self._D_magma = info_magma._D_magma
            else:
                self._O_magma = info_magma._O_magma.Order('%s'%self.level)

        if self.discriminant != 1:
            self._G_magma = magma.FuchsianGroup(self._O_magma.name())
            FDom_magma = self._G_magma.FundamentalDomain(self._D_magma.name())
            self._U_magma,_,self._m2_magma = self._G_magma.Group(nvals = 3)

        verbose('Spent %s seconds in init_magma_objects'%walltime(wtime))


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
        if self.discriminant != 1:
            return (self.basis_invmat * matrix(QQ,4,1,x.coefficient_tuple())).list()
        else:
            a,b,c,d = x.list()
            return [a, b, QQ(c)/self.level, d]

    def _is_in_order(self,x):
        return self._denominator(set_immutable(x)) == 1

    def _denominator(self,x):
        return lcm([ZZ(o.denominator()) for o in self._quaternion_to_list(x)])

    def _denominator_valuation(self,x,l):
        return max((o.denominator().valuation(l) for o in self._quaternion_to_list(x)))

    def _quaternion_to_magma_quaternion(self,x):
        v = list(x)
        return self._B_magma(v[0]) + sum(v[i+1]*self._B_magma.gen(i+1) for i in range(3))

    @cached_method
    def get_word_rep(self,delta):
        if self.discriminant == 1:
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
            if T[0,0] == -1:
                tmp.extend(self.minus_one)
            self.has_word_rep = True
        else:
            #verbose('Entering get_word_rep...')
            if not self._is_in_order(delta):
                raise RuntimeError,'delta (= %s) is not in order!'%delta
            try:
                c = self._get_word_recursive(delta,0)
            except RuntimeError:
                print '!! Resorted to Magma, indicates a bug (delta = %s,norm = %s)!!'%(delta,delta.reduced_norm())
                c = self._magma_word_problem(delta)
            tmp = [(g-1,len(list(a))) if g > 0 else (-g-1,-len(list(a))) for g,a in groupby(c)] # shorten_word(c)
            delta1 =  prod((self.Ugens[g]**a for g,a in tmp)) # Should be fixed...this is not efficient
            if delta1 != delta:
                tmp.extend(self.minus_one)
                delta1 =  prod((self.Ugens[g]**a for g,a in tmp)) # Should be fixed...this is not efficient
                assert delta1 == delta
        #verbose('done.')
        return tmp

    @cached_method
    def _get_word_recursive(self,delta,oldji,depth = 0):
        if depth > 100:
            raise RuntimeError
        B = delta.parent()
        if delta == B(1):
            return []
        elif delta == B(-1):
            return self.minus_one_long
        else:
            CC = ComplexField(200)
            P = CC(9)/CC(10) * CC.gen()
            emb = self.get_archimedean_embedding(200)
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


    @cached_method
    def _magma_word_problem(self,x):
        r'''
        Given a quaternion x, finds its decomposition in terms of the generators

        INPUT: x can be a list/vector of integers (giving the quaternion in terms of the basis for the order,
        or x can be a quaternion, in which case the conversion is done in the function.

        OUTPUT: A list representing a word in the generators

        EXAMPLES:

        sage: G = ArithGroup(7,15,1)
        sage: G._magma_word_problem(G.Ugens[2]*G.Ugens[1]) == [2,1]
        '''
        wtime = walltime()
        B = self.O
        x0 = x
        # If x is a quaternion, find the expression in the generators.
        if x.parent() is self.O or x.parent() is self.B:
            x = self._quaternion_to_magma_quaternion(x)
        else:
            if len(x) != 4:
                raise ValueError, 'x (=%s) should be a list of length 4'%x
            x = self._quaternion_to_magma_quaternion(sum(a*b for a,b in zip(self.Obasis,x)))
        x_magma = self._G_magma(x)
        #verbose('Calling _magma_word_problem with x = %s'%x)
        V = magma.WordProblem(x_magma).ElementToSequence()._sage_()
        delta1 = self.B(1)
        for v in V:
            delta1 = delta1 * self.Ugens[v - 1] if v > 0 else delta1 * self.Ugens[-v - 1]
        if delta1 != x0:
            V.extend(self.minus_one_long)
            delta1 = self.B(1)
            for v in V:
                delta1 = delta1 * self.Ugens[v - 1] if v > 0 else delta1 * self.Ugens[-v - 1]
        #verbose('Spent %s seconds in _magma_word_problem_'%wtime)
        return V

    def element_of_norm(self,N,use_magma = False,local_condition = None):
        try:
            return self._element_of_norm[N]
        except (AttributeError,KeyError):
            pass
        if not hasattr(self,'_element_of_norm'):
            self._element_of_norm  = dict([])
        if self.discriminant != 1:
            if use_magma:
                elt_magma = self._O_magma.ElementOfNorm(N*self._O_magma.BaseRing())
                candidate = self.B([QQ(elt_magma.Vector()[m+1]) for m in range(4)])
                if candidate.reduced_norm() != N:
                    candidate = candidate * self.element_of_norm(-1)
                self._element_of_norm[N] = candidate
                return candidate
            else:
                if local_condition is not None:
                    mat_inv = local_condition**-1
                    emb = self.get_embedding(20)
                v = self.O.gens()
                for a in product(range(-30,30),repeat = 4):
                    candidate = self.B(sum(ai*vi for ai,vi in  zip(a,v)))
                    if candidate.reduced_norm() == N:
                        self._element_of_norm[N] = candidate
                        if local_condition is not None and is_in_Gamma0loc(mat_inv * emb(candidate),det_condition = False):
                            return candidate
                        elif local_condition is None:
                            return candidate

        else:
            candidate = self.B([N,0,0,1])
            self._element_of_norm[N] = candidate
            return candidate

    def quaternion_algebra(self):
        return self.B

    def enumerate_elements(self,max_length = None):
        ngens = len(self.gens())
        for v in enumerate_words(range(ngens)):
            if max_length is not None and len(v) > max_length:
                raise StopIteration
            else:
                yield prod([self.gen(i) for i in v])

    @cached_method
    def get_hecke_reps(self,l):
        r'''
        TESTS:

        sage: magma.eval('SetSeed(2000000)')
        sage: G = ArithGroup(6,5)
        sage: reps = G.get_hecke_reps(11)
        '''
        if self.discriminant == 1: # or self.level % l == 0:
            reps = [self.B([l,i,0,1]) for i in range(l)] + [self.B([1,0,0,l])]
        else:
            g0 = self.element_of_norm(l,use_magma = True)
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
        if self.discriminant == 1 and self.level != 1:
            return None
        return self._gens[i]

    def gens(self):
        if self.discriminant == 1 and self.level != 1:
            raise NotImplementedError
        return self._gens

    @cached_method
    def image_in_abelianized(self, x):
        r''' Given an element x in Gamma, returns its image in the abelianized group'''
        Gab,V,free_idx = self.abelianization()
        if self.discriminant != 1:
            wd = x.word_rep
            tmp = Gab(sum(ZZ(a)*Gab(V.gen(g)) for g,a in wd))
        else:
            M = self.modsym_ambient
            f = self.modsym_map
            M1 = self.modsym_cuspidal
            a,b,c,d = x.quaternion_rep.list()
            tmp = Gab(M1.coordinate_vector(4*f(M([Cusps(Infinity),MatrixSpace(ZZ,2,2)(x.quaternion_rep) * Cusps(Infinity)]))))
        return (QQ**len(free_idx))([tmp[i] for i in free_idx])

    @cached_method
    def abelianization(self):
        if self.discriminant != 1:
            V = ZZ**len(self.gens())
            W = V.span([sum(a*v for a,v in zip(V.gens(),rel)) for rel in self.get_relation_matrix().rows()])
        else:
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

    def embed_order(self,p,D,prec,zero_deg = True,outfile = None):
        r'''
        sage: G = ArithGroup(5,6,1)
        sage: f = G.embed_order(23,20)
        sage: f0 = f.zero_degree_equivalent()
        '''
        if self.discriminant == 1:
            K_magma = magma.RadicalExtension(QQ,2,D)
        else:
            QQmagma = self._B_magma.BaseRing()#magma.RationalsAsNumberField()
            K_magma = magma.RadicalExtension(QQmagma,2,D) #self._B_magma.BaseField()
        OK_magma = K_magma.MaximalOrder()
        _,iota = magma.Embed(OK_magma,self._O_magma,nvals = 2)
        mu_magma = iota.Image(OK_magma(K_magma.gen(1)))
        Bgens = list(self.B.gens()) if self.discriminant != 1 else [matrix(QQ,2,2,[1,0,0,-1]),matrix(QQ,2,2,[0,1,1,0]),matrix(QQ,2,2,[0,1,-1,0])]
        mu = sum(a*b for a,b in zip([self.B(1)]+Bgens,[self._B_magma(mu_magma).Vector()[m+1].Norm()._sage_() for m in range(4)]))

        K = QuadraticField(D,names = 'kg')
        w = K.maximal_order().ring_generators()[0]
        Cp = Qp(p,prec).extension(w.minpoly(),names = 'g')
        r0,r1 = w.coordinates_in_terms_of_powers()(K.gen())
        v0 = K.hom([Cp(r0)+Cp(r1)*Cp.gen()])
        phi = K.hom([mu])
        fwrite('d_K = %s, h_K = %s, h_K^- = %s'%(K.discriminant(),K.class_number(),len(K.narrow_class_group())),outfile)
        fwrite('w_K satisfies: %s'%w.minpoly(),outfile)
        if self.discriminant == 1:
            assert K.gen(0).minpoly() == mu.minpoly()
            assert self._is_in_order(phi(w))

        iotap = self.get_embedding(prec)
        fwrite('Local embedding B to M_2(Q_p) sends i to %s and j to %s'%(iotap(self.B.gens()[0]).change_ring(Qp(p,5)).list(),iotap(self.B.gens()[1]).change_ring(Qp(p,5)).list()),outfile)
        a,b,c,d = iotap(mu).list()
        R = PolynomialRing(Cp,names = 'X')
        X = R.gen()
        tau = (Cp(a-d) + 2*v0(K.gen()))/Cp(2*c)
        # assert (c*tau**2 + (d-a)*tau-b) == 0

        found = False
        gamma = self(phi(K.units()[0])**2)
        fwrite('\cO_K to R_0 given by w_K |-> %s'%phi(w),outfile)
        fwrite('gamma_psi = %s'%gamma,outfile)
        fwrite('tau_psi = %s'%tau,outfile)
        fwrite('(where g satisfies: %s)'%w.minpoly(),outfile)
        return gamma, tau


class ArithGroupElement(MultiplicativeGroupElement):
    def __init__(self,parent, word_rep = None, quaternion_rep = None, check = True):
        r'''
        Initialize.

            INPUT:

            - a list of the form [(g1,a1),(g2,a2),...,(gn,an)] where the gi are indices
            refering to fixed generators, and the ai are integers, or
            an element of the quaternion algebra ``self.parent().quaternion_algebra()``
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
            if not parent._is_in_order(quaternion_rep):
                raise ValueError,'Quaternion must be in order'
            if check:
                rednrm = quaternion_rep.reduced_norm() if self.parent().discriminant != 1 else quaternion_rep.determinant()
                if rednrm != 1:
                    print quaternion_rep
                    raise ValueError,'Quaternion must be of norm 1'
            if check and not parent._is_in_order(quaternion_rep):
                    print quaternion_rep
                    raise ValueError,'Quaternion must be in order'
            self.quaternion_rep = set_immutable(quaternion_rep)
            self.has_quaternion_rep = True
            if word_rep is None:
                try:
                    self.word_rep = self._word_rep() # debug
                    self.has_word_rep = True
                except ValueError: pass
            init_data = True
        if init_data is False:
            raise ValueError,'Must pass either quaternion_rep or word_rep'
        self._reduce_word(check = check)

    def _repr_(self):
        return str(self.quaternion_rep)

    def _mul_(left,right):
        word_rep = None
        quaternion_rep = None
        # if left.has_word_rep and right.has_word_rep:
        #     word_rep = left.word_rep + right.word_rep
        if (left.has_quaternion_rep and right.has_quaternion_rep) or word_rep is None:
            quaternion_rep = left.quaternion_rep * right.quaternion_rep
        return ArithGroupElement(left.parent(),word_rep = word_rep, quaternion_rep = quaternion_rep, check = False)

    def is_one(self):
        quatrep = self.quaternion_rep
        return quatrep == 1

    def __invert__(self):
        word_rep = None
        quaternion_rep = None
        # if self.has_word_rep:
        #     word_rep = [(g,-i) for g,i in reversed(self.word_rep)]
        if self.has_quaternion_rep:
            quaternion_rep = self.quaternion_rep**(-1)
        return ArithGroupElement(self.parent(),word_rep = word_rep, quaternion_rep = quaternion_rep, check = False)

    def __cmp__(self,right):
        selfquatrep = self.quaternion_rep
        rightquatrep = right.quaternion_rep
        return selfquatrep.__cmp__(rightquatrep)

    def _reduce_word(self, check = True):
        if not self.has_word_rep:
            return
        if check:
            self.check_consistency(txt = '1')
        self.word_rep = reduce_word(self.word_rep)
        if check:
            self.check_consistency(txt = '2')

    #@lazy_attribute
    def _word_rep(self):
        r'''
        Returns a word in the generators of `\Gamma` representing the given quaternion `x`.
        '''
        tmp = self.parent().get_word_rep(self.quaternion_rep)
        self.has_word_rep = True
        self.check_consistency(self.quaternion_rep,tmp,txt = '3')
        return tmp

    @lazy_attribute
    def quaternion_rep(self):
        r'''
        Returns the quaternion representation.
        '''
        Gamma = self.parent()
        self.has_quaternion_rep = True
        return prod((Gamma.gen(g).quaternion_rep**a for g,a in self.word_rep), z = Gamma.B(1))

    def check_consistency(self, q = None, wd = None,txt = ''):
        if q is None and wd is None:
            if not self.has_quaternion_rep or not self.has_word_rep:
                return
        if q is None:
            q = self.quaternion_rep
        if wd is None:
            wd = self.word_rep
        Gamma = self.parent()
        q1 = prod(Gamma.Ugens[g]**a for g,a in wd)
        if q != q1:
            print q
            print q1
            print q * q1**-1
            raise RuntimeError,'Word and quaternion are inconsistent! (%s)'%txt
        return

    def get_weight_vector(self):
        gens = self.parent().gens()
        weight_vector = vector(ZZ,[0 for g in gens])
        for i,a in self.word_rep:
            weight_vector[i] += a
        return weight_vector

    def __getitem__(self,n):
        r'''
        Returns the nth letter of the form g^a
        '''
        g,a = self.word_rep[n]
        return self.parent().gen(g)**a

    def is_trivial_in_abelianization(self):
        return self.get_weight_vector() in self.parent().get_relation_matrix().image()

    def _calculate_weight_zero_word(self):
        if not self.is_trivial_in_abelianization():
            raise ValueError,'Element must be trivial in the abelianization'
        G = self.parent()
        wt = self.get_weight_vector()
        relmat = G.get_relation_matrix()
        relwords = G.get_relation_words()
        num_rels = len(relwords)
        f= (ZZ**num_rels).hom(relmat.rows())
        linear_combination = f.lift(wt)
        verbose('linear combination = %s'%linear_combination)
        oldword = copy(self.word_rep)
        for i,lam in enumerate(linear_combination):
            relation = relwords[i]
            verbose('lam = %s'%lam)
            if lam == 0:
                continue
            elif lam < 0:
                oldword += ZZ((-lam))*relation
            else: #lam > 0
                oldword += ZZ(lam)*[(g,-j) for g,j in reversed(relation)]
        tmp = reduce_word(oldword)
        assert self.parent()(tmp).get_weight_vector() == 0
        return tmp
