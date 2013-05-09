##########################################################################
### Stark-Heegner points for quaternion algebras (following M.Greenberg)
##########################################################################
from sage.groups.group import AlgebraicGroup
from sage.structure.element import MultiplicativeGroupElement
import itertools
from collections import defaultdict
from itertools import product,chain,izip,groupby,islice,tee,starmap
from sage.modular.pollack_stevens.distributions import Distributions, Symk
from sage.modular.pollack_stevens.sigma0 import Sigma0,Sigma0ActionAdjuster

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

class _our_adjuster(Sigma0ActionAdjuster):
    """
    Callable object that turns matrices into 4-tuples.

    EXAMPLES::

        sage: from sage.modular.btquotients.pautomorphicform import _btquot_adjuster
        sage: adj = _btquot_adjuster()
        sage: adj(matrix(ZZ,2,2,[1..4]))
        (4, 2, 3, 1)
    """
    def __call__(self, g):
        a,b,c,d = g.list()
        return tuple([d,b,c,a])

def is_in_Sigma0(x):
    if x.determinant() == 0:
        return False
    a,b,c,d = _our_adjuster()(x)
    if c.valuation() < 1:
        return False
    if a.valuation() != 0:
        return False
    if b.valuation() < 0 or d.valuation() < 0:
        return False
    return True

sys.setrecursionlimit(10**6)

def set_immutable(x):
    try:
        x.set_immutable()
        return x
    except AttributeError:
        return x

def GG(x,y):
    return [(1,x,y),(-1,y,x),(-1,y*x,(y*x)**-1),(1,x*y,(y*x)**-1)]

def act_flt(g,x):
    a,b,c,d = g.list()
    return (a*x + b)/(c*x + d)

def act_flt_in_disc(g,x,P):
    z = (P.conjugate()*x - P)/(x-1)
    a,b,c,d = g.list()
    z1 = (a*z + b)/(c*z + d)
    return (z1 - P)/(z1 - P.conjugate())

def translate_into_twosided_list(V):
    vp,vm = V
    return [None] + vp + list(reversed(vm))

def getcoords(E,u,prec,R = None):
    if R is None:
        R = u.parent()
        u = R(u)
    p = R.prime()
    jE = E.j_invariant()

    # Calculate the Tate parameter
    E4 = EisensteinForms(weight=4).basis()[0]
    Delta = CuspForms(weight=12).basis()[0]
    j = (E4.q_expansion(prec+7))**3/Delta.q_expansion(prec+7)
    qE =  (1/j).power_series().reversion()(R(1/jE))

    # Normalize the period by appropriate powers of qE
    un = u * qE**(-(u.valuation()/qE.valuation()).floor())

    precn = (prec/qE.valuation()).floor() + 4
    # formulas in Silverman II (Advanced Topics in the Arithmetic of Elliptic curves, p. 425)
    xx = un/(1-un)**2 + sum( [qE**n*un/(1-qE**n*un)**2 + qE**n/un/(1-qE**n/un)**2-2*qE**n/(1-qE**n)**2 for n in range(1,precn) ])
    yy = un**2/(1-un)**3 + sum( [qE**(2*n)*un**2/(1-qE**n*un)**3 - qE**n/un/(1-qE**n/un)**3+qE**n/(1-qE**n)**2 for n in range(1,precn) ])


    sk = lambda q,k,pprec: sum( [n**k*q**n/(1-q**n) for n in range(1,pprec+1)] )
    n = qE.valuation()
    precp = ((prec+4)/n).floor() + 2;

    tate_a4 = -5  * sk(qE,3,precp)
    tate_a6 = (tate_a4 - 7 * sk(qE,5,precp) )/12
    Eq = EllipticCurve([R(1),R(0),R(0),tate_a4,tate_a6])

    C2 = (Eq.c4() * E.c6()) / (Eq.c6() * E.c4())

    C = our_sqrt(R(C2),R) #R(C2).square_root()
    s = (C - R(E.a1()))/R(2)
    r = (s*(C-s) - R(E.a2())) / 3
    t =  (r*(2*s-C)-R(E.a3())) / 2
    return  ( r + C2 * xx, t + s * C2 * xx + C * C2 * yy )

def our_sqrt(x,K):
    if x==0:
        return x
    x=K(x)
    p=K.base_ring().prime()
    valp = x.valuation(p)
    try:
        eK = K.ramification_index()
    except AttributeError:
        eK = 1
    valpi = eK * valp
    if valpi % 2 != 0:
        raise RuntimeError,'Not a square'
    x = p**(-valp) * x
    z = K.gen()
    deg = K.degree()
    found = False
    for avec in product(range(p),repeat=deg):
        y0 = avec[0]
        for a in avec[1:]:
            y0 = y0*z + a
        if (y0**2-x).valuation() > 0:
            found = True
            break
    if found == False:
        raise RuntimeError,'Not a square'
    y1 = y0
    y = 0
    while y != y1:
        y = y1
        y1 = (y**2+x)/(2*y)
    return K.uniformizer()**(ZZ(valpi/2)) * y

def enumerate_words(v, n = None):
    if n is None:
        n = []
    while True:
        add_new = True
        for jj in range(len(n)):
            n[jj] += 1
            if n[jj] != len(v):
                add_new = False
                break
            else:
                n[jj] = 0
        if add_new:
            n.append(0)
        yield [v[x] for x in n]

def cantor_diagonal(iter1,iter2):
    v1 = [iter1.next()]
    v2 = [iter2.next()]
    while True:
        for a,b in zip(v1,v2):
            yield a,b
        v1.append(iter1.next())
        v2.insert(0,iter2.next())

def shorten_word(longword):
    r'''
    Converts a word in Magma format into our own format.

        TESTS:

            sage: short = shorten_word([1,1,-3,-3,-3,2,2,2,2,2,-1,-1,-1])
            sage: print short
            [(0, 2), (2, -3), (1, 5), (0, -3)]
    '''
    return [(a-1,len(list(g))) if a > 0 else (-a-1,-len(list(g))) for a,g in groupby(longword)]

def reduce_word(word):
    r'''
    Simplifies the given word by cancelling out [g^a, g^b] -> [g^(a+b)],
    and [g^0] -> []
    '''
    new_word = copy(word)
    old_word = []
    while len(new_word) != len(old_word):
        old_word = new_word
        for i in range(len(old_word)-1):
            if old_word[i][0] == old_word[i+1][0]:
                new_exp = old_word[i][1]+old_word[i+1][1]
                if new_exp != 0:
                    new_word = old_word[:i]+[(old_word[i][0],new_exp)]+old_word[i+2:]
                else:
                    new_word = old_word[:i]+old_word[i+2:]
                break
    return new_word

def is_in_Gamma0loc(A,det_condition = True):
    r'''
    Whether the matrix A has all entries Zp-integral, and is upper-triangular mod p.
    '''
    if det_condition == True and A.determinant() != 1:
        return False
    return all([o.valuation() >=0 for o in A.list()]) and A[1,0].valuation() > 0

class ArithGroupAction(sage.categories.action.Action):
    def __init__(self,G,M):
        sage.categories.action.Action.__init__(self,G,M,is_left = True,op = operator.mul)

    def _call_(self,g,v):
        K = v.parent().base_ring()
        iota = g.parent().get_embedding(K.precision_cap())
        a,b,c,d = iota(g.quaternion_rep).change_ring(K).list()
        newdict = defaultdict(ZZ)
        for P,n in v._data.iteritems():
            newdict[(a*P+b)/(c*P+d)] += n #K0(a)*P+K0(b))/(K0(c)*P+K0(d))] += n
        return v.parent()(newdict)

class BigArithGroup(AlgebraicGroup):
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
    def __init__(self,p,discriminant,level,seed = 1000000):
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
        verbose('Initializing arithmetic group G(pn)...')
        self.Gpn = ArithGroup(discriminant,p*level,info_magma = self.Gn)
        self.Gpn.get_embedding = self.get_embedding
        self._prec = -1
        self.get_Up_reps()
        verbose('Done initializing arithmetic groups')
        self.Gpn.get_Up_reps = self.get_Up_reps
        verbose('Done initialization of BigArithmeticGroup')

    def _repr_(self):
        return 'Big Arithmetic Group attached to data p = %s,  disc = %s, level = %s'%(self.p,self.discriminant,self.level)

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

        wtime = walltime()
        verbose('Calling pMatrixRing...')

        M,f,_ = magma.pMatrixRing(self.Gn._O_magma.name(),prime*self.Gn._ZZ_magma,nvals = 3)
        verbose('Spent %s seconds in pMatrixRing'%walltime(wtime))
        QQp = Qp(prime,prec)
        self._prec = prec
        B_magma = self.Gn._B_magma
        v = f.Image(B_magma.1).Vector()
        self._II = matrix(QQp,2,2,[v[i+1]._sage_() for i in range(4)])
        v = f.Image(B_magma.2).Vector()
        self._JJ = matrix(QQp,2,2,[v[i+1]._sage_() for i in range(4)])
        v = f.Image(B_magma.3).Vector()
        self._KK = matrix(QQp,2,2,[v[i+1]._sage_() for i in range(4)])
        # Test splitting
        for g in self.Gpn.Obasis:
            tup = g.coefficient_tuple()
            mat = tup[0] + tup[1]* self._II + tup[2]*self._JJ + tup[3]*self._KK
            assert is_in_Gamma0loc(mat,det_condition = False)

        return self._II, self._JJ, self._KK

    @cached_method
    def get_BT_reps(self):
        reps = [self.Gn.B(1)]
        for n_iters,elt0 in enumerate(self.Gn.enumerate_elements()):
            if n_iters % 100 == 0:
                verbose('%s, len = %s/%s'%(n_iters,len(reps),self.p+1))
            elt = elt0.quaternion_rep
            new_inv = elt**(-1)
            if all([not self.Gpn._is_in_order(old * new_inv) for old in reps]):
                reps.append(set_immutable(elt))
                if len(reps) == self.p + 1:
                    return reps

    def do_hat(self,g):
        return self.wp * g * self.wp**-1

    def do_tilde(self,g):
        return QQ(-1/self.p) * self.wp * g * self.wp

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
            emb = self.get_embedding(20)
            for v1,v2 in cantor_diagonal(self.Gn.enumerate_elements(),self.Gn.enumerate_elements()):
                new_candidate =   v2.quaternion_rep * tmp *  v1.quaternion_rep
                if is_in_Gamma0loc(epsinv * emb(new_candidate), det_condition = False):
                    if all([self.Gpn._is_in_order(new_candidate**-1 * g * new_candidate) for g in self.Gpn.Obasis]):
                        return new_candidate

    @lazy_attribute
    def wp_magma(self):
        if all([kronecker_symbol(-self.p,a) != 1 for a,r in factor(self.discriminant)]):
            rootminusp = True
            K_magma = magma.RadicalExtension(self.Gpn._B_magma.BaseField(),2,-self.p)
            OK_magma = K_magma.MaximalOrder()
            _,iota = magma.Embed(OK_magma,self.Gpn._O_magma,nvals = 2)
        elif all([kronecker_symbol(self.p,a) != 1 for a,r in factor(self.discriminant)]):
            assert 0
            rootminusp = False
            K_magma = magma.RadicalExtension(self.Gpn._B_magma.BaseField(),2,self.p)
            OK_magma = K_magma.MaximalOrder()
            _,iota = magma.Embed(OK_magma,self.Gpn._O_magma,nvals = 2)
        else:
            raise ValueError,'Quaternion algebra not compatible with \pm p'

        mu_magma = iota.Image(OK_magma(K_magma.1))
        Bgens = list(self.Gpn.B.gens())
        mu = sum(a*b for a,b in zip([self.Gpn.B(1)]+Bgens,[self.Gpn._B_magma(mu_magma).Vector()[m+1].Norm()._sage_() for m in range(4)]))
        assert all([self.Gpn._is_in_order(mu**-1 * g * mu) for g in self.Gpn.Obasis])
        if rootminusp is True:
            assert is_in_Gamma0loc(matrix(QQ,2,2,[0,-1,self.p,0])**-1 * self.get_embedding(20)(mu))
        else:
            assert is_in_Gamma0loc(matrix(QQ,2,2,[0,1,self.p,0])**-1 * self.get_embedding(20)(mu))
        verbose('Done!')
        return mu

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
                if type(q) is tuple:
                    v = q
                else:
                    v = q.coefficient_tuple()
                return R(v[0] + I*v[1] + J*v[2] + K*v[3])
        else:
            R =  Qp(self.p,prec)
            def iota(q):
                return q.apply_map(lambda x:R(x))
        return iota

    def _mult_word(self,a,wd):
        r'''
        EXAMPLES:
        '''
        x1 = a
        for j,i in wd:
            g = self.get_BT_reps()[j]
            if i == 1: #and j != 0:
                g = self.do_tilde(g)
            x1 = x1 * g
        return x1

    def reduce_in_amalgam(self,x,return_word = False, check = False):
        rednrm = x.reduced_norm() if self.discriminant != 1 else x.determinant()
        if rednrm != 1:
            raise ValueError,'x (= %s) must have reduced norm 1'%x
        a,wd = self._reduce_in_amalgam(set_immutable(x))
        if check == True:
            assert x == self._mult_word(a,wd)
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
        x = set_immutable(p**-(rednrm.valuation(p)/2) * x)
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
            a,wd = G._reduce_in_amalgam(x)
            return a, wd + [wd1,wd0]

    def construct_cycle(self,D,prec,hecke_smoothen = None):
        gamma, tau = self.Gn.embed_order(self.p,D,prec)
        Div = DivisorsOnHp(tau.parent())
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
                verbose('...')
                n += 1
                gamman *= gamma
        if hecke_smoothen is not None:
            tmp = tmp.hecke_smoothen(hecke_smoothen,prec = prec)
        return tmp,n

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
            emb = self.get_archimedean_embedding(100)
            self.gquats = translate_into_twosided_list([[self.B([self._B_magma(gquats_magma[i+1][n+1].Quaternion()).Vector()[m+1] for m in range(4)]) for n in range(len(gquats_magma[i+1]))] for i in range(2)])
            self.embgquats =  [None] + [emb(g) for g in self.gquats[1:]]

            self.pi = RealField(100)(4*arctan(1))
            self.findex = [ZZ(x._sage_()) for x in self._G_magma.get_magma_attribute('ShimGroupSidepairsIndex')]
            self.fdargs = [RealField(100)(x._sage_()) for x in self._G_magma.get_magma_attribute('ShimFDArgs')]

            self.minus_one_long = [ len(self.Ugens) + 1 ]
            self.minus_one = shorten_word(self.minus_one_long)
            self.Ugens.append(self.B(-1))

            self.translate = [None] + [self._magma_word_problem(g**-1) for g in self.gquats[1:]]

            self._gens = [ArithGroupElement(self,quaternion_rep = g, word_rep = [(i,1)],check = False) for i,g in enumerate(self.Ugens)]

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
                self._ZZ_magma = QQ_magma.Integers()
                if hasattr(self,'abtuple'):
                    self._B_magma = magma.QuaternionAlgebra('%s'%QQ_magma.name(),self.abtuple[0],self.abtuple[1])
                else:
                    self._B_magma = magma.QuaternionAlgebra('%s*%s'%(self.discriminant,self._ZZ_magma.name()))

                self._O_magma = self._B_magma.MaximalOrder().Order('%s*%s'%(self.level,self._ZZ_magma.name()))
                self._D_magma = magma.UnitDisc(Precision = 100)
            else:
                self._ZZ_magma = magma.Integers()
                self._B_magma = magma.QuaternionAlgebra(magma.Rationals(),1,1)
                self._O_magma = self._B_magma.MaximalOrder().Order('%s'%self.level)
        else:
            self._ZZ_magma = info_magma._B_magma.BaseRing().Integers()
            self._B_magma = info_magma._B_magma
            if self.discriminant != 1:
                self._O_magma = info_magma._O_magma.Order('%s*%s'%(self.level,self._ZZ_magma.name()))
                self._D_magma = info_magma._D_magma
            else:
                self._O_magma = info_magma._O_magma.Order('%s'%self.level)

        if self.discriminant != 1:
            self._G_magma = magma.FuchsianGroup(self._O_magma.name())
            self._FDom_magma = self._G_magma.FundamentalDomain(self._D_magma.name())
            self._U_magma,self._m1_magma,self._m2_magma = self._G_magma.Group(nvals = 3)

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
            v = f.Image(B_magma.1).Vector()
            self._II_inf = matrix(RR,2,2,[v[i+1]._sage_() for i in range(4)])
            v = f.Image(B_magma.2).Vector()
            self._JJ_inf = matrix(RR,2,2,[v[i+1]._sage_() for i in range(4)])
            v = f.Image(B_magma.3).Vector()
            self._KK_inf = matrix(RR,2,2,[v[i+1]._sage_() for i in range(4)])
        return self._II_inf, self._JJ_inf, self._KK_inf

    def _quaternion_to_list(self,x):
        if self.discriminant != 1:
            return (self.basis_invmat * matrix(QQ,4,1,x.coefficient_tuple())).list()
        else:
            a,b,c,d = x.list()
            return [a, b, c/self.level, d]

    def _is_in_order(self,x):
        return self._denominator(set_immutable(x)) == 1

    def _denominator(self,x):
        return lcm([ZZ(o.denominator()) for o in self._quaternion_to_list(x)])

    def _denominator_valuation(self,x,l):
        return max((o.denominator().valuation(l) for o in self._quaternion_to_list(x)))

    def _list_to_quaternion(self,x):
        return sum(a*b for a,b in zip(self.Obasis,x))

    def _list_to_magma_quaternion(self,x):
        return self._quaternion_to_magma_quaternion(self._list_to_quaternion(x))

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
                decomp = continued_fraction_list(a/c)
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
                verbose('!! Resorted to Magma, indicates a bug !!')
                c = self._magma_word_problem(delta)
            tmp = [(a-1,len(list(g))) if a > 0 else (-a-1,-len(list(g))) for a,g in groupby(c)] # shorten_word(c)
            delta1 =  prod(self.Ugens[g]**a for g,a in tmp) # Should be fixed...this is not efficient
            if delta1 != delta:
                tmp.extend(self.minus_one)
        #verbose('done.')
        return tmp

    #@cached_method
    def _get_word_recursive(self,delta,oldji,depth = 0):
        if depth > 100:
            raise RuntimeError
        if delta == 1:
            return []
        elif delta == -1:
            return self.minus_one_long
        else:
            CC = ComplexField(200)
            P = 9/10 * CC.gen()
            z0 = 0
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
                i = next(j for j,fda in enumerate(fdargs) if az0 <= fda)
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
            x = self._list_to_magma_quaternion(x)
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
                elt_magma = self._O_magma.ElementOfNorm(N*self._ZZ_magma)
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
            g0 = self.element_of_norm(l)
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
        #verbose('gk1 = %s, gamma = %s, l = %s'%(gk1,gamma,l))
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
            V = ZZ^len(self.gens())
            W = V.span([sum(a*v for a,v in zip(V.gens(),rel)) for rel in self.get_relation_matrix().rows()])
        else:
            self.modsym_ambient = ModularSymbols(self.level,sign = 1)
            self.modsym_cuspidal = self.modsym_ambient.cuspidal_subspace()[0]
            self.modsym_map = self.modsym_cuspidal.projection()
            ngens = self.modsym_cuspidal.dimension()
            V = ZZ^ngens
            W = V.span([])

        Gab = V/W
        free_idx = []
        for i in range(len(Gab.invariants())):
            if Gab.invariants()[i] == 0:
                free_idx.append(i)
        return Gab,V,free_idx

    def embed_order(self,p,D,prec,zero_deg = True,seed = None):
        r'''
        sage: G = ArithGroup(5,6,1)
        sage: f = G.embed_order(23,20)
        sage: f0 = f.zero_degree_equivalent()
        '''
        if self.discriminant == 1:
            K_magma = magma.RadicalExtension(QQ,2,D)
        else:
            K_magma = magma.RadicalExtension(self._B_magma.BaseField(),2,D)
        OK_magma = K_magma.MaximalOrder()
        _,iota = magma.Embed(OK_magma,self._O_magma,nvals = 2)
        mu_magma = iota.Image(OK_magma(K_magma.1))
        Bgens = list(self.B.gens()) if self.discriminant != 1 else [matrix(QQ,2,2,[1,0,0,-1]),matrix(QQ,2,2,[0,1,1,0]),matrix(QQ,2,2,[0,1,-1,0])]
        mu = sum(a*b for a,b in zip([self.B(1)]+Bgens,[self._B_magma(mu_magma).Vector()[m+1].Norm()._sage_() for m in range(4)]))

        K = QuadraticField(D,names = 'kg')
        w = K.maximal_order().ring_generators()[0]
        Cp = Qp(p,prec).extension(w.minpoly(),names = 'g')
        r0,r1 = w.coordinates_in_terms_of_powers()(K.gen())
        v0 = K.hom([Cp(r0)+Cp(r1)*Cp.gen()])
        phi = K.hom([mu])

        if self.discriminant == 1:
            assert K.gen(0).minpoly() == mu.minpoly()
            self._is_in_order(phi(w))

        iotap = self.get_embedding(prec)
        a,b,c,d = iotap(mu).list()
        R.<X> = PolynomialRing(Cp)
        tau = (Cp(a-d) + 2*v0(K.gen()))/Cp(2*c)
        # assert (c*tau**2 + (d-a)*tau-b) == 0

        found = False
        gamma = self(phi(K.units()[0])**2)
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
        G = self.parent()
        weight_vector = vector(ZZ,len(G.gens()),[0 for ii in range(len(G.gens()))])
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
        f= (ZZ^num_rels).hom(relmat.rows())
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

######################
##                  ##
##    COHOMOLOGY    ##
##                  ##
######################

def apply_hecke_operator(coh_group,c,l,fix_first_moments = False,hecke_reps = None,group = None,scale = 1):
    r"""
    Apply the l-th Hecke operator operator to ``c``.

    EXAMPLES::

    """
    if hecke_reps is None:
        hecke_reps = coh_group.group().get_hecke_reps(l)
    V = coh_group.coefficient_module()
    if V.base_ring().is_exact():
        prec = 200
    else:
        prec = V.base_ring().precision_cap()

    Gpn = coh_group.group()
    group = Gpn
    emb = Gpn.get_embedding(prec)
    vals = []
    if fix_first_moments:
        try:
            orig_moments = [v._moments[0] for v in c.values()]
        except IndexError:
            orig_moments = [V(0) for v in c.values()]
    R = V.base_ring()
    if hasattr(coh_group.coefficient_module(),'dimension'):
        gammas = []
        Gab,Vmod,free_idx = Gpn.abelianization()
        for i in free_idx:
            idxlist = list(Gab.gen(i).lift())
            gammas.append(prod([t**a for a,t in zip(idxlist,Gpn.gens()) if a != 0]))
    else:
        gammas = Gpn.gens()

    for j,gamma in enumerate(gammas):
        newval = V(0)
        for gk1 in hecke_reps:
            tig = group.get_hecke_ti(gk1,gamma.quaternion_rep,l,reps = hecke_reps)
            val0 = c.evaluate(tig)
            try:
                newval += coh_group._Sigma0(emb(gk1)) * val0
            except AttributeError:
                newval += val0
        if fix_first_moments:
            try:
                newval._moments[0] = orig_moments[j] # only works for weight 0!
            except TypeError:
                pass
        vals.append(scale * newval)
    return coh_group(vals)


class CohomologyTrivialCoeffsClass(ModuleElement):
    def __init__(self, parent, data):
        r'''
        Define an element of `H^1(G,ZZ)`

        INPUT:
            - G: a BigArithGroup
            - V: a CoeffModule
            - data: a list

        TESTS:
            sage: G = BigArithGroup(5,6,1)
            sage: V = QQ^1
            sage: Coh = Cohomology(G,V)
            sage: print Coh.hecke_matrix(13).eigenvalues()
            [2,2]
            sage: print Coh.hecke_matrix(7).eigenvalues()
            [4,-4]
            sage: PhiE = Coh.gen(1)
        '''
        G = parent.group()
        V = parent.coefficient_module()
        if isinstance(data,list):
            self._val = [V(o) for o in data]
        else:
            self._val = [V(data.evaluate(b)) for b in parent._space.domain().basis()]
        ModuleElement.__init__(self,parent)

    def values(self):
        return self._val

    def _repr_(self):
        return 'Cohomology class %s'%self._val

    def  _add_(self,right):
        return self.__class__(self.parent(),[a+b for a,b in zip(self._val,right._val)])

    def  _sub_(self,right):
        return self.__class__(self.parent(),[a-b for a,b in zip(self._val,right._val)])

    def  _neg_(self):
        return self.__class__(self.parent(),[-a for a in self._val])

    def  __rmul__(self,right):
        return self.__class__(self.parent(),[ZZ(right) * a for a in self._val])

    def shapiro_image(self,G):
        return ShapiroImage(G,self)

    @cached_method
    def evaluate(self,x):
        word = tuple(x.word_rep)
        G = self.parent().group()
        V = self.parent().coefficient_module()
        return sum([a*self._evaluate_at_group_generator(g) for g,a in word],V(0))

    @cached_method
    def _evaluate_at_group_generator(self,j): # j is the index in Gpn.gens()
        Gab, V0,free_idx = self.parent().group().abelianization()
        coeff_module = self.parent().coefficient_module()
        tmp = Gab(V0.gen(j))
        gablist = [tmp[i] for i in free_idx]
        assert sum(1 if a0 != 0 else 0 for a0 in gablist) <= 1
        cvals = [coeff_module(o) for o in self._val]
        val0 = sum((ZZ(a0) * b for a0,b in zip(gablist,cvals) if a0 != 0),coeff_module(0))
        return val0

class CohomologyTrivialCoeffs(Parent):
    Element = CohomologyTrivialCoeffsClass
    def __init__(self,G,n,base = None):
        self._group = G
        if base is None:
            base = QQ
        self._coeffmodule = base**1
        self._Ga,self._V,self._free_idx = G.abelianization()
        self._num_abgens = len(self._free_idx)
        self._F = QQ**self._num_abgens
        self._space = Hom(self._F,self._coeffmodule)
        Parent.__init__(self)

    def _an_element_(self):
        return self.gen(0)

    def _element_constructor_(self,data):
        if isinstance(data,list):
            return self.element_class(self,data)
        elif isinstance(data.parent(),Cohomology):
            V = self.coefficient_module()
            tmp = []
            for i in self._free_idx:
                idxlist = list(self._Ga.gen(i).lift())
                tmp.append([a*data.evaluate(t).moment(0).rational_reconstruction() for a,t in zip(idxlist,self.group().gens()) if a != 0])
            return self.element_class(self,tmp)
        else:
            raise RuntimeError

    def _coerce_map_from_(self,S):
        if isinstance(S,(Cohomology,CohomologyTrivialCoeffs)):
            return True
        else:
            return False

    def construct_element_from_vector(self,v):
        return sum([a*self.gen(i) for i,a in enumerate(v) if a != 0],self(self._num_abgens * [0]))

    def group(self):
        return self._group

    def _repr_(self):
        return 'H^1(G,V), with G being %s and V = %s'%(self.group(),self.coefficient_module())

    def coefficient_module(self):
        return self._coeffmodule

    def basis(self):
        return self._space.basis()

    def group_rank(self):
        return self._num_abgens

    def dimension(self):
        return len(self.basis())

    def gen(self,i):
        phi = self.basis()[i]
        dom = phi.domain()
        return self([phi(o) for o in dom.gens()])

    def gens(self):
        return [self.gen(i) for i in range(self.dimension())]

    @cached_method
    def hecke_matrix(self,l):
        if self._group.discriminant == 1:
            raise NotImplementedError
        if self.coefficient_module().dimension() > 1:
            raise NotImplementedError
        H = self._space
        Gpn = self.group()
        dim = self.dimension()
        gprank = self.group_rank()
        R = self.coefficient_module().base_ring()
        M = matrix(R,dim,dim,0)
        for j,cocycle in enumerate(self.gens()):
            # Construct column j of the matrix
            Tc = [o[0] for o in self.apply_hecke_operator(cocycle,l).values()]
            # Tc = []
            # for i in self._free_idx:
            #     idxlist = list(self._Ga.gen(i).lift())
            #     Tc.append([a*t[0] for a,t in zip(idxlist,tmp) if a != 0])
            M.set_column(j,Tc)
        return M

    def apply_hecke_operator(self,c,l,hecke_reps = None,group = None,scale = 1):
        r"""
        Apply the l-th Hecke operator operator to ``c``.
        """
        return apply_hecke_operator(self,c,l,hecke_reps = hecke_reps, group = group,scale = scale)

    @cached_method
    def involution_at_infinity_matrix(self):
        emb = self.group().get_embedding(20)
        H = self._space
        Gpn = self.group()
        Obasis = Gpn.Obasis
        for V in product(range(-5,6),repeat = len(Obasis)):
            x = sum((v*o for v,o in zip(V,Obasis)))
            rednrm = x.reduced_norm() if self.group().discriminant != 1 else x.determinant()
            if rednrm == -1:
                found = True
                break
        assert found
        dim = self.dimension()
        M = matrix(QQ,dim,dim,0)
        for j,c in enumerate(self.gens()):
            # Construct column j of the matrix
            for i in range(dim):
                ti = x**-1 * prod([Gpn.gen(idx)**a for idx,a in zip(range(len(Gpn.gens())),list(self._Ga.gen(self._free_idx[i]).lift()))]).quaternion_rep * x
                tmp = Gpn(ti)
                M[i,j] = c.evaluate(tmp)[0]
        return M

##########################
#
# Nontrivial coefficients
#
##########################

class CohomologyClass(ModuleElement):
    def __init__(self, parent, data):
        r'''
        Define an element of `H^1(G,V)`

        INPUT:
            - G: a BigArithGroup
            - V: a CoeffModule
            - data: a list

        TESTS:

            sage: G = BigArithGroup(5,6,1)
            sage: V = QQ^1
            sage: Coh = Cohomology(G,V)
            sage: print Coh.hecke_matrix(13).eigenvalues()
            [2,2]
            sage: print Coh.hecke_matrix(7).eigenvalues()
            [4,-4]
            sage: PhiE = Coh.gen(1)
        '''
        G = parent.group()
        V = parent.coefficient_module()
        if not isinstance(data,list):
            raise ValueError,'Expecting a list'
        if len(data) != len(G.gens()):
            raise ValueError,'Passed %s values, need %s'%(len(data),len(G.gens()))
        self._val = [V(o) for o in data]
        ModuleElement.__init__(self,parent)

    def values(self):
        return self._val

    def _repr_(self):
        return 'Cohomology class %s'%self._val

    def  _add_(self,right):
        return self.__class__(self.parent(),[a+b for a,b in zip(self._val,right._val)])

    def  _sub_(self,right):
        return self.__class__(self.parent(),[a+ ZZ(-1)*b for a,b in zip(self._val,right._val)])

    def  _neg_(self):
        return self.__class__(self.parent(),[ZZ(-1) * a for a in self._val])

    def  __rmul__(self,right):
        return self.__class__(self.parent(),[ZZ(right) * a for a in self._val])

    def evaluate(self,x):
        if x.parent() is not self.parent().group():
            x = self.parent().group()(x)
        return self.evaluate_word(tuple(x.word_rep))

    @cached_method
    def evaluate_word(self,word):
        r''' Evaluate recursively, using cocycle condition:
        self(gh) = self(g) + g*self(h)
        This implies also that:
        1) self(g^a) = self(g^b) + g^b*self(g^(a-b)) (will apply it to b = a // 2, a > 0
        2) self(g^-1) = - g^(-1)*self(g)
        '''
        # verbose('evaluating word %s'%list(word))
        G = self.parent().group()
        V = self.parent().coefficient_module()
        Sigma0 = self.parent()._Sigma0
        if len(word) == 0:
            return V(0)
        emb = G.get_embedding(200)
        if len(word) == 1:
            g,a = word[0]
            if a == 0:
                return V(0)
            elif a == -1:
                return -(Sigma0(emb(G.gen(g).quaternion_rep**-1)) * self._val[g])
            elif a < 0:
                return -(Sigma0(emb(G.gen(g).quaternion_rep**a)) * self.evaluate_word(tuple([(g,-a)])))
            elif a == 1:
                return self._val[g]
            else:
                phig = self._val[g]
                tmp = V(phig)
                for i in range(a-1):
                    tmp = phig + Sigma0(emb(G.gen(g).quaternion_rep)) * tmp
                return tmp
        else:
            pivot = len(word) // 2
            gamma = prod([G.gen(g).quaternion_rep**a for g,a in word[:pivot]],G.B(1))
            return self.evaluate_word(tuple(word[:pivot])) + Sigma0(emb(gamma)) *  self.evaluate_word(tuple(word[pivot:]))


    def improve(self,group = None,prec = None,sign = 1):
        r"""
        Repeatedly applies U_p.

        EXAMPLES::

        """
        MMM = self.parent()
        U = MMM.coefficient_module()
        p = U.base_ring().prime()
        if group is None:
            group = self.parent().group()
        if prec is None:
            prec = U.precision_cap()
        reps = group.get_Up_reps()
        h2 = MMM.apply_hecke_operator(self,p,fix_first_moments = False, hecke_reps = reps,group = group,scale = sign)
        verbose('%s'%h2,level = 2)
        verbose("Applied Up once")
        ii = 0
        current_val = min([(h2._val[i] - self._val[i]).valuation() for i in range(len(h2._val))])
        old_val = -Infinity
        while current_val < prec and current_val > old_val:
            h1 = h2
            old_val = current_val
            ii += 1
            h2 = MMM.apply_hecke_operator(h1,p, fix_first_moments = False, hecke_reps = reps,group = group,scale = sign)
            verbose('%s'%h2,level = 2)

            current_val = min([(h2._val[i] - h1._val[i]).valuation() for i in range(len(h2._val))])
            verbose('Applied Up %s times (val = %s)'%(ii+1,current_val))
        self._val = h2._val
        verbose('Final precision of %s digits'%current_val)
        return h2

class Cohomology(Parent):
    Element = CohomologyClass
    def __init__(self,G,n,overconvergent = False,base = None):
        assert n == 0
        self._group = G
        if overconvergent and base is None:
            raise ValueError, 'Must give base if overconvergent'
        if base is None:
            base = QQ
        if not overconvergent:
            self._coeffmodule = Symk(n,base = base, act_on_left = True,adjuster = _our_adjuster(), dettwist = 0) # Darmon convention
        else:
            self._coeffmodule = Distributions(n,base = base, prec_cap = base.precision_cap(), act_on_left = True,adjuster = _our_adjuster(), dettwist = 0) # Darmon convention
        self._Sigma0 = self._coeffmodule._act._Sigma0
        Parent.__init__(self)

    def _an_element_(self):
        return self([0] * len(self.group().gens()))

    def _element_constructor_(self,data):
        if isinstance(data,list):
            if len(data) != len(self.group().gens()):
                raise ValueError
            return self.element_class(self,data)
        elif data.parent() is self:
            return self.element_class(self,data._val)
        elif data.parent() is CohomologyTrivialCoeffs:
            G = self.group()
            V = self.coefficient_module()
            return self.element_class(self,[V(data.evaluate(g)) for g in G.gens()])
        else:
            raise ValueError

    def _coerce_map_from_(self,S):
        if isinstance(S,Cohomology):
            return True
        elif isinstance(S,CohomologyTrivialCoeffs):
            return True
        else:
            return False

    def group(self):
        return self._group

    def _repr_(self):
        return 'H^1(G,V), with G being %s and V = %s'%(self.group(),self.coefficient_module())

    def coefficient_module(self):
        return self._coeffmodule

    def apply_hecke_operator(self,c,l,fix_first_moments = False, hecke_reps = None,group = None,scale = 1):
        r"""
        Apply the l-th Hecke operator operator to ``c``.
        """
        return apply_hecke_operator(self,c,l,fix_first_moments = fix_first_moments,hecke_reps = hecke_reps, group = group,scale = scale)


class ShapiroImage(SageObject):
    def __init__(self,G,cocycle):
        self.G = G
        self.cocycle = cocycle

    def __call__(self,gamma):
        return CoinducedElement(self.G,self.cocycle,gamma)

class CoinducedElement(SageObject):
    def __init__(self,G,cocycle,gamma):
        self.G = G
        self.cocycle = cocycle
        self.gamma = gamma

    def __call__(self,h,check = False):
        rev, b = h
        if check:
            assert self.G.reduce_in_amalgam(b,check = True) == 1
        a = self.G.reduce_in_amalgam(b * self.gamma,check = check)
        elt = self.G.Gpn(a)
        tmp = self.cocycle.evaluate(elt)
        if rev == False:
            return tmp
        else:
            return -tmp

######################
##                  ##
##     HOMOLOGY     ##
##                  ##
######################

class DivisorsOnHp(Parent):
    def __init__(self,field):
        self._field = field
        Parent.__init__(self)

    def _an_element_(self):
        return DivisorOnHp(self,[(3,self._field._an_element_())])

    def _element_constructor_(self,data):
        return DivisorOnHp(self,data)

    def _coerce_map_from_(self,S):
        if isinstance(S,DivisorOnHp):
            return S._field is self._field
        else:
            return False

    def base_field(self):
        return self._field

    def base_ring(self):
        return self._field

    def _repr_(self):
        return 'Group of divisors on Hp, over ' + self._field._repr_()


class DivisorOnHp(ModuleElement):
    def __init__(self,parent,data):
        r'''
        A Divisor is given by a list of pairs (P,nP), where P is a point, and nP is an integer.

        TESTS:

            sage: Cp.<g> = Qq(5^3,20)
            sage: Div = DivisorsOnHp(Cp)
            sage: D1 = Div(g+3)
            sage: D2 = Div(2*g+1)
            sage: D = D1 + D2
            sage: print -D
            sage: print 2*D1 + 5*D2
        '''

        self._data = defaultdict(ZZ)
        ModuleElement.__init__(self,parent)
        if data == 0:
            return
        if isinstance(data,list):
            for n,P in data:
                if n == 0:
                    continue
                self._data[P] += n
                if self._data[P] == 0:
                    del self._data[P]
        elif isinstance(data,dict):
            self._data.update(data)
        else:
            P = self.parent().base_field()(data)
            self._data[P] = 1

    def _repr_(self):
        return 'Divisor on Hp of degree %s'%self.degree()

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
            mystr += '%s*(%s)'%(n,P)
        return mystr

    def __cmp__(self,right):
        return self._data.__cmp__(right._data)

    def is_zero(self):
        return all((n == 0 for n in self._data.itervalues()))

    def _add_(self,right):
        newdict = defaultdict(ZZ)
        newdict.update(self._data)
        for P,n in right._data.iteritems():
            newdict[P] += n
            if newdict[P] == 0:
                del newdict[P]
        return DivisorOnHp(self.parent(),newdict)

    def _sub_(self,right):
        newdict = defaultdict(ZZ)
        newdict.update(self._data)
        for P,n in right._data.iteritems():
            newdict[P] -= n
            if newdict[P] == 0:
                del newdict[P]
        return DivisorOnHp(self.parent(),newdict)

    def _neg_(self):
        return DivisorOnHp(self.parent(),dict((P,-n) for P,n in self._data.iteritems()))

    def left_act_by_matrix(self,g):
        a,b,c,d = g.list()
        return DivisorOnHp(self.parent(),dict(((P.parent()(a)*P+P.parent()(b))/(P.parent()(c)*P+P.parent()(d)),n) for P,n in self._data.iteritems()))

    @cached_method
    def degree(self):
        return sum(self._data.itervalues())

    @cached_method
    def size(self):
        return sum(ZZ(d).abs() for d in self._data.itervalues())

    def support(self):
        return Set([d for d in self._data])

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
        #V.register_action(ArithGroupAction(G.Gn,V))
        #V.register_action(ArithGroupAction(G.Gpn,V))
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
            sage: Div = DivisorsOnHp(Cp)
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
            if v.degree() == 0:
                newdict[oldg] += v
            else:
                newv = v
                gword = oldg._calculate_weight_zero_word()
                for i,a in gword:
                    g = G.gen(i)
                    oldv = newv
                    newv = (g^-a) * oldv
                    if a < 0:
                        a = -a
                        oldv = (g^a) * oldv
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
        return HomologyClass(self.parent(),newdict)

    def _check_cycle_condition(self):
        res = self.parent().coefficient_module()(0)
        for g,v in self._data.iteritems():
            res += (g**-1) * v - v
        if res.is_zero():
            return True
        else:
            print res.value()
            return False

    def mult_by(self,a):
        return self.__rmul__(a)

    def hecke_smoothen(self,r,prec = 20):
        return self.act_by_hecke(r,prec = prec) - self.mult_by(r+1)

    def __rmul__(self,a):
        if a == 0:
            return HomologyClass(self.parent(),dict([]))
        else:
            return HomologyClass(self.parent(),dict(((g,a*v) for g,v in self._data.iteritems())))

######################
##                  ##
##  INTEGRATION     ##
##                  ##
######################

r'''
Integration pairing. The input is a cycle (an element of `H_1(G,\text{Div}^0)`)
and a cocycle (an element of `H^1(G,\text{HC}(\ZZ))`).
Note that it is a multiplicative integral.
'''
def integrate_H1(G,cycle,cocycle,depth,method = 'moments',smoothen_prime = 0,tohat = True):
    res = 1
    R.<t> = PolynomialRing(cycle.parent().coefficient_module().base_field())
    emb = G.get_embedding(prec)
    wpa,wpb,wpc,wpd = emb(G.wp).change_ring(R.base_ring()).list()
    if method == 'moments':
        integrate_H0 = integrate_H0_moments
    else:
        assert method == 'riemann'
        integrate_H0 = integrate_H0_riemann
    jj = 0
    for g,divisor in cycle.get_data():
        jj += 1
        print 'Integral %s...'%jj
        if divisor.degree() != 0:
            raise ValueError,'Divisor must be of degree 0'
        if tohat:
            fd = prod([(t - (wpa*P +wpb)/(wpc*P+wpd))**ZZ(n) for P,n in divisor._data.iteritems()],R(1))
            tmp = integrate_H0(G,fd,cocycle,depth = depth,gamma = G.do_hat(g.quaternion_rep))
        else:
            fd = prod([(t - P)**ZZ(n) for P,n in divisor._data.iteritems()],R(1))
            tmp = integrate_H0(G,fd,cocycle,depth = depth,gamma = g.quaternion_rep)
        res *= tmp
    return res

r'''
Integration pairing of a function with an harmonic cocycle.
'''
def riemann_sum(G,phi,hc,depth = 1,cover = None,mult = False):
    p = G.p
    prec = max([20,2*depth])
    emb = G.get_embedding(prec)
    res = 1 if mult else 0
    K = phi(0).parent().base_ring()
    if cover is None:
        cover = G.get_covering(depth)
    n_ints = 0
    for e in cover:
        if n_ints % 500 == 499:
            verbose('Done %s percent'%(100*RealField(10)(n_ints)/len(cover)))
        n_ints += 1
        val = hc(e)
        vmom = val[0] #.moment(0)
        if vmom.parent().is_exact():
            hce = ZZ(vmom)
        else:
            hce = ZZ(vmom.rational_reconstruction())
        if hce == 0:
            continue
        #verbose('hc = %s'%hce)
        te = sample_point(G,e,prec)
        if te == Infinity:
            continue
        if mult:
            res *= phi(K(te))**hce
        else:
            res += phi(K(te)) * hce
    return res

def integrate_H0_riemann(G,phi,hc,depth = 1,cover = None,gamma = None):
    return riemann_sum(G,phi,hc.shapiro_image(G)(gamma),depth,cover,mult = True)

def integrate_H0_moments(G,phi,hc,depth = None, cover = None,gamma = None):
    p = G.p
    prec = hc.parent().coefficient_module().precision_cap()
    K = phi.parent().base_ring()
    R = PolynomialRing(K,'x')
    x = R.gen()
    R1 = LaurentSeriesRing(K,'r1')
    r1 = R1.gen()
    R1.set_default_prec(prec)
    emb = G.get_embedding(prec)
    resadd = 0
    for h in G.get_BT_reps_twisted():
        a,b,c,d = emb(h**-1).change_ring(K).list()
        y0 = phi((a*r1+b)/(c*r1+d))
        val = y0(0)
        assert all([xx.valuation(p) > 0 for xx in (y0/val - 1).list()])
        pol = val.log() + (y0.derivative()/y0).integral()
        mu_e = hc.evaluate(G.reduce_in_amalgam(h * gamma,check = True))
        nmoments = len(mu_e._moments)
        resadd += sum(a*mu_e.moment(i) for a,i in izip(pol.coefficients(),pol.exponents()) if i < nmoments)
    HOC = hc.parent()
    Htriv = CohomologyTrivialCoeffs(HOC.group(),0,base = QQ)
    resmul = integrate_H0_riemann(G,phi,Htriv(hc),depth = 1,gamma = gamma)
    val =  resmul.valuation(p)
    tmp = p**val * K.teichmuller(p**(-val)*resmul)
    if resadd != 0:
         tmp *= resadd.exp()
    return tmp

def sample_point(G,e,prec = 20):
    r'''
     Returns a point in U_h = (e)^{-1} Z_p.
    '''
    rev, h = e
    hemb = G.get_embedding(prec)(h**-1)
    wploc = G.get_embedding(prec)(G.wp)
    if rev == True:
        hemb = hemb * wploc
    a,b,c,d = hemb.list()
    if d == 0:
        return Infinity
    return b/d

def measure_test(G,hc,E):
    p = G.p
    prec = 20
    res = 0
    n_ints = 0
    for e in E:
        n_ints += 1
        hce = hc(e).moment(0)
        res += hce
    return res


def points_test(G,level):
    p = G.p
    prec = 20
    K.<tau> = Qq(p^2,prec)
    tau1 = K.gen()
    tau2 = tau1+1
    emb = G.get_embedding(prec)
    res = 0
    E = G.get_covering(level)
    for e in E:
        te = sample_point(G,e,prec)
        if te == Infinity:
            continue
        for e1 in G.subdivide([e],(level) % 2,1):
            te1 = sample_point(G,e1,prec)
            if te1 == Infinity:
                continue
            thisval = (((te-tau1)/(te-tau2)) / ((te1-tau1)/(te1-tau2)) - 1).valuation()
            if  thisval < level:
                print thisval
