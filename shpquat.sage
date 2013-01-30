##########################################################################
### Stark-Heegner points for quaternion algebras (following M.Greenberg)
##########################################################################
from sage.groups.group import AlgebraicGroup
from sage.structure.element import MultiplicativeGroupElement
import itertools
from collections import defaultdict
from itertools import product,chain,izip,groupby,islice,tee
from sage.modular.pollack_stevens.fund_domain import M2Z

sys.setrecursionlimit(10**6)

magma.eval('SetSeed(1000000)')

def set_immutable(x):
    try:
        x.set_immutable()
        return
    except AttributeError:
        return

def lift_to_sl2z(symb):
    M = MatrixSpace(ZZ,2,2)
    m = M(1)
    for n,S in symb.manin_symbol_rep():
        m = m * M(S.lift_to_sl2z())**ZZ(n)
    return m

def pairwise(iterable):
    "s -> (s0,s1), (s2,s3), ... "
    a = iter(iterable)
    return izip(a, a)

def shift_word(wd,n):
    return [(a+n,i) for a,i in wd]

def invert_word(wd):
    return [(g,-i) for g,i in reversed(wd)]

def GG(x,y):
    return [(1,x,y),(-1,y,x),(-1,y*x,(y*x)**-1),(1,x*y,(y*x)**-1)]

def evaluate_cocycle(G,Phi,tau,emb,gamma1,gamma2,level):
    tau0 = tau
    a,b,c,d = emb(gamma1 ** -1).list()
    tau1 = (a*tau0 + b)/(c*tau0 + d)
    fd1 = lambda t: 1 if t == Infinity else (t-tau1)/(t-tau0)
    return integrate_H0(G,fd1,Phi(gamma2),level)

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

def period_from_coords(p,E, P, prec = 20):
    r"""
    Given a point `P` in the formal group of the elliptic curve `E` with split multiplicative reduction,
    this produces an element `u` in `\QQ_p^{\times}` mapped to the point `P` by the Tate parametrisation.
    The algorithm return the unique such element in `1+p\ZZ_p`.

    INPUT:

    - ``P`` - a point on the elliptic curve.

    - ``prec`` - the `p`-adic precision, default is 20.

    """
    R = Qp(p,prec)
    # if P[0].valuation(p) >= 0:
    #     raise  ValueError , "The point must lie in the formal group."
    Etate = E.tate_curve(p)
    Eq = Etate.curve(prec = prec)
    isom = Etate._isomorphism(prec=prec)
    C = isom[0]
    r = isom[1]
    s = isom[2]
    t = isom[3]
    xx = r + C**2 * P[0]
    yy = t + s * C**2 * P[0] + C**3 * P[1]
    try:
        EqCp = Eq.change_ring(yy.parent())
        Pq = EqCp([xx,yy])
    except:
        raise RuntimeError, "Bug : Point %s does not lie on the curve "%[xx,yy]

    tt = -xx/yy
    eqhat = Eq.formal()
    eqlog = eqhat.log(prec + 3)
    z = eqlog(tt)
    u = ZZ(1)
    fac = ZZ(1)
    for i in range(1,2*prec+1):
        fac = fac * i
        u = u + z**i/fac
    q = Etate.parameter(prec = prec)
    un = u * q**(-(u.valuation()/q.valuation()).floor())
    return un

def getcoords(E,u,prec=20,R = None):
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

def dimension_harmonic_cocycles(k,lev ,Nplus):
    r"""
    This function computes the dimension of the space of harmonic cocycles
    of weight `k` on ``self``.

    OUTPUT:

      An integer equal to the dimension
    """

    k = ZZ(k)
    lev = ZZ(lev)
    Nplus = ZZ(Nplus)

    if k == 0:
        return 0

    if lev == 1:
        return Gamma0(Nplus).dimension_cusp_forms(k = k)

    f = lev.factor()
    if any([l[1] != 1 for l in f]):
        raise NotImplementedError, 'The level should be squarefree for this function to work... Sorry!'

    return Gamma0(lev*Nplus).dimension_cusp_forms(k = k) - sum([len(ZZ(lev/d).divisors())*dimension_harmonic_cocycles(k,d,Nplus) for d in lev.divisors()[:-1]])


# print [(p,dimension_harmonic_cocycles(2,6*p,1)) for p in range(5,100) if ZZ(p).is_prime()]
# Examples: discriminant = 6, and p = 5, 7, 13


r'''
Converts a word in Magma format into our own format.

    TESTS:

    sage: short = shorten_word([1,1,-3,-3,-3,2,2,2,2,2,-1,-1,-1])
    sage: print short
    [(0, 2), (2, -3), (1, 5), (0, -3)]
'''
def shorten_word(longword):
    return [(a-1,len(list(g))) if a > 0 else (-a-1,-len(list(g))) for a,g in groupby(longword)]

r'''
Simplifies the given word by cancelling out [g^a, g^b] -> [g^(a+b)],
and [g^0] -> []
'''
def reduce_word(word):
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

def big_commutator(v):
    if len(v) == 0:
        return 1
    x,y= v[0],v[1]
    return x * y * x**-1 * y**-1 * big_commutator(v[2:])

def big_commutator_seq(v):
    if len(v) == 0:
        return []
    x,y= v[0],v[1]
    xinv = [(g,-i) for g,i in reversed(x)]
    yinv = [(g,-i) for g,i in reversed(y)]
    return reduce_word(x + y + xinv + yinv + big_commutator_seq(v[2:]))

def quat_commutator(x,y):
    return x*y*x**-1*y**-1

r'''
    TESTS:
    sage: G = ArithGroup(5,6,5)
    sage: a = G([(1,2),(0,3),(2,-1)])
    sage: b = G([(1,3),(2,-1),(0,2)])
    sage: c = commutator(a,b)
'''
def commutator(x,y):
    if x.parent() is not y.parent():
        raise ValueError,'x and y must have same parent'
    return ArithGroupCommutator(x.parent(),x,y)

class ArithGroupAction(sage.categories.action.Action):
    def __init__(self,G,M,is_left = True): #,get_embedding = None):
        if not isinstance(G,ArithGroup):
            raise ValueError
        if not isinstance(M,DivisorsOnHp):
            raise ValueError
        # if get_embedding is None:
        #     self.get_embedding = lambda prec: (lambda x:x)
        # else:
        #     self.get_embedding = get_embedding
        sage.categories.action.Action.__init__(self,G,M,is_left,operator.mul)

    def _call_(self,g,v):
        if not self.is_left():
            g,v = v,g
        #iota = self.get_embedding(v.parent().base_field().precision_cap())
        iota = g.parent().get_embedding(v.parent().base_field().precision_cap())
        a,b,c,d = iota(g.quaternion_rep).list()

        newdict = defaultdict(ZZ)
        for P,n in v._data.iteritems():
            newdict[(a*P+b)/(c*P+d)] += n
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
    def __init__(self,p,discriminant,level):
        self.p = ZZ(p)
        if not self.p.is_prime():
            raise ValueError, 'p ( = %s) must be prime'%self.p
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
        self.Gpn.reduce_in_amalgam = self.reduce_in_amalgam
        self.Gpn._mult_word = self._mult_word
        self.gis = [ g**-1 for g in self.get_BT_reps()]
        self._prec = -1
        #self.wp = self._wp()

        self.gihats = [ self.wp**-1 * g * self.wp for g in self.gis]
        verbose('Done initialization of BigArithmeticGroup')


    # def __call__(self,x):
    #     return self.Gn.__call__(x)

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
        self._prec=prec
        B_magma = self.Gn._B_magma
        v = f.Image(B_magma.1).Vector()
        self._II = matrix(QQp,2,2,[v[i+1]._sage_() for i in range(4)])
        v = f.Image(B_magma.2).Vector()
        self._JJ = matrix(QQp,2,2,[v[i+1]._sage_() for i in range(4)])
        v = f.Image(B_magma.3).Vector()
        self._KK = matrix(QQp,2,2,[v[i+1]._sage_() for i in range(4)])
        return self._II, self._JJ, self._KK


    r'''
    Finds representatives for Gamma_0(p) \backslash Gamma_0. This means that
    a g \sim g for all a in Gamma_0(p).

    TESTS:

    sage: G = BigArithGroup(5,6,1)
    sage: reps = G.get_BT_reps()
    sage: G = BigArithGroup(7,5*11,3)
    sage: reps = G.get_BT_reps()
    '''
    @cached_method
    def get_BT_reps(self):
        if self.level % self.p == 0:
            raise NotImplementedError
        reps = [self.Gn.B(1)]
        ngens = len(self.Gn.gens())
        I = enumerate_words(range(ngens))
        n_iters = ZZ(0)
        while len(reps) < self.p + 1:
            n_iters += 1
            if n_iters%100 == 0:
                verbose('%s, len = %s/%s'%(n_iters,len(reps),self.p+1))
            v = I.next()
            new_candidate = prod([self.Gn.gen(i).quaternion_rep for i in v])
            new_inv = new_candidate**(-1)
            if not any([self.Gpn._is_in_order(old * new_inv) for old in reps]):
                set_immutable(new_candidate)
                reps.append(new_candidate)
        return reps

    @cached_method
    def get_BT_reps_twisted(self):
        return [self.wp**-1 * g * self.wp for g in self.get_BT_reps()]

    def get_covering(self,depth):
        w = self.wp
        return self.subdivide([(-1, o) for i,o in enumerate(self.get_BT_reps())], depth - 1)

    def subdivide(self,edgelist,depth):
        if depth < 0:
            return []
        if depth == 0:
            for i,e in edgelist:
                set_immutable(e)
            return edgelist
        w = self.wp
        newEgood=[]
        for i,edge in edgelist:
            if i == -1:
                newEgood.extend([(-i, w**-1 * e * w * edge) for e in self.get_BT_reps()[1:]])
            else:
                newEgood.extend([(-i, e * edge) for e in self.get_BT_reps()[1:]])
        return self.subdivide(newEgood,depth - 1)


    ## Make sure that it normalizes the suborder.
    @lazy_attribute
    def wp(self):
        if self.discriminant == 1:
            return matrix(QQ,2,2,[0,-1,self.p,0])
        else:
            tmp = self.Gn.element_of_norm(self.p)
        emb = self.get_embedding(20)
        ngens = len(self.Gn.gens())
        I = enumerate_words(range(ngens))
        n_iters = ZZ(0)
        while True:
            n_iters += 1
            if n_iters%100 == 0:
                verbose('%s'%(n_iters))
            v = I.next()
            new_candidate =  tmp * prod([self.Gn.gen(i).quaternion_rep for i in v])
            if all([self.Gpn._is_in_order(new_candidate **-1 * g * new_candidate) for g in self.Gpn.Obasis]):
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
                v=q.coefficient_tuple()
                return R(v[0] + I*v[1] + J*v[2] + K*v[3])
        else:
            R =  Qp(self.p,prec)
            def iota(q):
                return q.apply_map(lambda x:R(x))
        return iota


    r'''
    sage: G = BigArithGroup(5,6,1)
    sage: greps = G.get_BT_reps()
    sage: wp = G.wp
    sage: test_word = wp**-1*greps[1]*wp * greps[4] * wp**-1*greps[2]*wp * greps[3] * wp**-1 *greps[1]*wp *greps[3] *wp**-1*greps[2]*wp * greps[3] * wp**-1 *greps[1]*wp *greps[5]
    sage: x,wd = G.reduce_in_amalgam(test_word,return_word = True,check=True)
    sage: test_word = wp**-1*greps[0]*wp  * greps[5]
    sage: x,wd = G.reduce_in_amalgam(test_word,return_word = True,check=True)

    '''
    def _mult_word(self,a,wd):
        x1 = a
        wp = self.wp
        for j,i,new_factor in wd:
            g = self.get_BT_reps()[j]
            if i == 1:
                g = wp**-1 * g * wp
            assert new_factor == g
            x1 = x1 * new_factor
        return x1

    def reduce_in_amalgam(self,x,return_word = False, check = False):
        rednrm = x.reduced_norm() if self.discriminant != 1 else x.determinant()
        if rednrm != 1:
            raise ValueError,'x (= %s) must have reduced norm 1'%x

        set_immutable(x)
        if check == True:
            a,wd = self._reduce_in_amalgam(x,return_word = True)
            assert x == self._mult_word(a,wd)
            if return_word == True:
                return a,wd
            else:
                return a
        else:
            if return_word == True:
                a,wd = self._reduce_in_amalgam(x,return_word = True)
                return a,wd
            else:
                a = self._reduce_in_amalgam(x,return_word = False)
                return a

    # @cached_method
    def _reduce_in_amalgam(self,x,return_word = False):
        #verbose('x = %s'%x)
        x0 = x
        emb = self.get_embedding(20)
        wp = self.wp
        p = self.p
        rednrm = x.reduced_norm() if self.discriminant != 1 else x.determinant()
        btreps = self.get_BT_reps()
        btrepshat = self.get_BT_reps_twisted()
        denval = self.Gn._denominator_valuation

        x = p**-(rednrm.valuation(p)/2) * x
        set_immutable(x)
        if self.Gpn._denominator(x) == 1:
            if return_word == False:
                return x
            else:
                return x,[]
        else:
            gis = self.gis
            gihats = self.gihats
            xhat = wp**-1 * x * wp

            valx = denval(xhat,p)
            if valx == 0:
                valx = 1
            found = False

            i = next((i for i,g in enumerate(gihats) if denval(xhat * g,p) < valx),0)
            wd0 = (i,0,btreps[i])
            x = x * gis[i]

            valx = denval(x,p)
            if valx == 0:
                valx = 1

            i = next((i for i,g in enumerate(gihats) if denval(x * g,p) < valx),0)
            wd1 = (i,1,btrepshat[i])
            x = x * gihats[i]

            if return_word == False:
                set_immutable(x)
                a = G._reduce_in_amalgam(x,return_word = return_word)
                return a
            else:
                set_immutable(x)
                a,wd = G._reduce_in_amalgam(x,return_word = return_word)
                return a, wd + [wd1,wd0]

    r'''
    sage: G = ArithGroup(5,6,1)
    sage: f = G.embed_order(23,20)
    sage: f0 = f.zero_degree_equivalent()
    '''
    def embed_order(self,D,prec):
        if self.discriminant == 1:
            K_magma = magma.RadicalExtension(QQ,2,D)
        else:
            K_magma = magma.RadicalExtension(self.Gn._B_magma.BaseField(),2,D)
        OK_magma = K_magma.MaximalOrder()
        _,iota = magma.Embed(OK_magma,self.Gn._O_magma,nvals = 2)
        mu_magma = iota.Image(OK_magma(K_magma.1))
        Bgens = list(self.Gn.B.gens()) if self.discriminant != 1 else [matrix(QQ,2,2,[1,0,0,-1]),matrix(QQ,2,2,[0,1,1,0]),matrix(QQ,2,2,[0,1,-1,0])]
        mu = sum(a*b for a,b in zip([self.Gn.B(1)]+Bgens,[self.Gn._B_magma(mu_magma).Vector()[m+1].Norm()._sage_() for m in range(4)]))

        K = QuadraticField(D,names = 'kg')

        w = K.maximal_order().ring_generators()[0]
        Cp = Qp(self.p,prec).extension(w.minpoly(),names = 'g')
        r0,r1 = w.coordinates_in_terms_of_powers()(K.gen())
        v0 = K.hom([r0+r1*Cp.gen()])
        phi = K.hom([mu])

        if self.discriminant == 1:
            assert K.gen(0).minpoly() == mu.minpoly()
            self.Gn._is_in_order(phi(w))

        iotap = self.get_embedding(prec)
        a,b,c,d = iotap(mu).list()
        R.<X> = PolynomialRing(Cp)
        # tau = (c*X^2+(d-a)*X-b).roots(Cp)[0][0]
        tau = (a-d + 2*v0(K.gen()))/(2*c)
        assert (c*tau**2 + (d-a)*tau-b) == 0

        gamma = self.Gn(phi(K.units()[0]**2))
        Div = DivisorsOnHp(Cp)
        D1 = Div(tau)
        D1 = Div(tau)
        H1 = Homology(self,Div)
        n = 1
        gamman = gamma
        while n < 100:
            try:
                tmp = H1(dict([(gamman,D1)])).zero_degree_equivalent()
                verbose('n = %s'%n)
                return tmp
            except ValueError:
                n += 1
                gamman *= gamma
        raise RuntimeError,'Went past n = 100 !'

class ArithGroup(AlgebraicGroup):
    def __init__(self,discriminant,level,info_magma = None):
        self.discriminant = ZZ(discriminant)
        self.level = ZZ(level)

        self._prec_inf = -1

        if len(self.discriminant.factor()) % 2 != 0:
            raise ValueError, 'Discriminant must contain an even number of primes'

        self._init_magma_objects(info_magma)
        if self.discriminant != 1:
            self.B = QuaternionAlgebra((self._B_magma.gen(1)**2)._sage_(),(self._B_magma.gen(2)**2)._sage_())
            assert self.B.discriminant() == discriminant
            self.O = self.B.quaternion_order([self.B([QQ(self._O_magma.ZBasis()[n+1].Vector()[m+1]) for m in range(4)]) for n in range(4)])
            self.Obasis = self.O.basis()
            self.basis_invmat = matrix(QQ,4,4,[list(self.O.gen(n)) for n in range(4)]).transpose().inverse() # !!!
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

            found = False
            for i1,g1 in enumerate(self.Ugens):
                for i2,g2 in enumerate(self.Ugens):
                    if g1 * g2 == -1:
                        self.minus_one_long = [i1 + 1, i2 + 1]
                        self.minus_one = shorten_word(self.minus_one_long)
                        found = True
                        break
                if found:
                    break
            assert found

            self._gens = [ArithGroupElement(self,quaternion_rep = self.Ugens[i], word_rep = [(i,1)],check = False) for i in range(len(self.Ugens))]

            self.translate = [None] + [self._magma_word_problem(g**-1) for g in self.gquats[1:]]


            temp_relation_words = [shorten_word(self._U_magma.Relations()[n+1].LHS().ElementToSequence()._sage_()) for n in range(len(self._U_magma.Relations()))]
        else:
            self.B = MatrixSpace(QQ,2,2)
            self.Obasis = [matrix(ZZ,2,2,v) for v in [[1,0,0,0],[0,1,0,0],[0,0,self.level,0],[0,0,0,1]]]
            self.Ugens = [self.B([1,1,0,1]), self.B([1,0,level,1])]
            self._gens = [ArithGroupElement(self,quaternion_rep = self.Ugens[i], word_rep = [(i,1)],check = False) for i in range(len(self.Ugens))]
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
                self._relation_words.append(reduce_word(2*rel))
            else:
                assert 0

        # Define the relation matrix
        self._relation_matrix = matrix(ZZ,len(self._relation_words),len(self.Ugens),0)
        for i,rel in enumerate(self._relation_words):
            for j,k in rel:
                self._relation_matrix[i,j] += k
        Parent.__init__(self)

    def _an_element_(self):
        return self.gen(0)

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
        else:
            return ArithGroupElement(self, quaternion_rep = x)
            #raise ValueError

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
                self._ZZ_magma = magma.RationalsAsNumberField().Integers()
                self._B_magma = magma.QuaternionAlgebra('%s*%s'%(self.discriminant,self._ZZ_magma.name()))
                self._O_magma = self._B_magma.MaximalOrder().Order('%s*%s'%(self.level,self._ZZ_magma.name()))
                self._D_magma = magma.UnitDisc( Precision = 100)
            else:
                self._ZZ_magma = magma.Integers()
                self._B_magma = magma.QuaternionAlgebra(magma.Rationals(),1,1)
                self._O_magma = self._B_magma.MaximalOrder().Order('%s'%self.level)
        else:
            self._ZZ_magma = info_magma._B_magma.BaseRing().Integers()
            self._B_magma = info_magma._B_magma
            if self.discriminant != 1:
                self._O_magma = info_magma._O_magma.Order('%s*%s'%(self.level,self._ZZ_magma.name()))
                self._D_magma = info_magma._D_magma # magma.UnitDisc( Precision = 100)
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
        set_immutable(x)
        return self._denominator(x) == 1

    def _denominator(self,x):
        return lcm([ZZ(o.denominator()) for o in self._quaternion_to_list(x)])

    def _denominator_valuation(self,x,p):
        return max((o.denominator().valuation(p) for o in self._quaternion_to_list(x)))

    def _list_to_quaternion(self,x):
        return sum(a*b for a,b in zip(self.Obasis,x))

    def _list_to_magma_quaternion(self,x):
        O = self.O
        return self._quaternion_to_magma_quaternion(self._list_to_quaternion(x))

    def _quaternion_to_magma_quaternion(self,x):
        v = list(x)
        return self._B_magma(v[0]) + sum([v[i+1]*self._B_magma.gen(i+1) for i in range(3)])

    # @cached_method
    def get_word_rep(self,delta):
        if self.discriminant == 1:
            level = self.level
            assert level == 1
            a,b,c,d = delta.list()
            m1 = matrix(ZZ,2,2,[1,0,0,1])

            if c != 0:
                decomp = continued_fraction_list(a/c)
                if len(decomp) % 2 == 1:
                    decomp[-1] -= 1
                    decomp.append(1)

                tmp = []

                for r,s in pairwise(decomp):
                    tmp.extend([(0,r),(1,s)])
                    m1 = m1 * matrix(ZZ,2,2,[1,r,0,1]) * matrix(ZZ,2,2,[1,0,s,1])
            T = m1**-1 * delta
            assert ( T[0,0] == 1 and T[1,1] == 1 and T[1,0] == 0) or ( T[0,0] == -1 and T[1,1] == -1 and T[1,0] == 0)
            tmp.append((0,T[0,0]*T[0,1]))
            if T[0,0] == -1:
                tmp.extend(self.minus_one)

            self.has_word_rep = True
            return tmp
        else:
            c = self._get_word_recursive(delta,0)
            tmp = [(a-1,len(list(g))) if a > 0 else (-a-1,-len(list(g))) for a,g in groupby(c)] # shorten_word(c)
            delta1 =  prod(self.Ugens[g]**a for g,a in tmp) # Should be fixed...this is not efficient
            if delta1 != delta:
                tmp.extend(self.minus_one)
            #assert self.get_word_rep_old(delta) == tmp
        return tmp

    # @cached_method
    def _get_word_recursive(self,delta,oldji):
        if delta == 1:
            return []
        elif delta == -1:
            return self.minus_one_long
        else:
            # CC = ComplexField(100)
            P = 9/10 * CC.gen()
            z0 = 0
            emb = self.get_archimedean_embedding(100)
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
            tmp = newcs + self._get_word_recursive(delta,oldji)
            return tmp


    r'''
    Given a quaternion x, finds its decomposition in terms of the generators

    INPUT: x can be a list/vector of integers (giving the quaternion in terms of the basis for the order,
    or x can be a quaternion, in which case the conversion is done in the function.

    OUTPUT: A list representing a word in the generators

    EXAMPLES:

    sage: G = ArithGroup(7,15,1)
    sage: G._magma_word_problem(G.Ugens[2]*G.Ugens[1]) == [2,1]
    '''
    @cached_method
    def _magma_word_problem(self,x):
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
            # if delta1 != x0:
            #     print delta1
            #     print x0
            #     print delta1/x0
            #     assert 0
        #verbose('Spent %s seconds in _magma_word_problem_'%wtime)
        return V

    def element_of_norm(self,N):
        if self.discriminant != 1:
            elt_magma = self._O_magma.ElementOfNorm(N*self._ZZ_magma)
            return self.B([QQ(elt_magma.Vector()[m+1]) for m in range(4)])
        else:
           return self.B([N,0,0,1])

    def quaternion_algebra(self):
        return self.B

    r'''
    TESTS:

    sage: magma.eval('SetSeed(2000000)')
    sage: G = ArithGroup(6,5)
    sage: reps = G.get_hecke_reps(11)
    '''
    @cached_method
    def get_hecke_reps(self,l):
        if self.discriminant != 1:
            g0 = self.element_of_norm(l)
            reps = [g0]
            ngens = len(self.gens())
            I = enumerate_words(range(ngens))
            n_iters = ZZ(0)
            while len(reps) < l + 1:
                n_iters += 1
                if n_iters % 10 == 0:
                    verbose('%s, len = %s/%s'%(n_iters,len(reps),l + 1))
                v = I.next()
                new_candidate_sage = prod([self.gen(i).quaternion_rep for i in v]) * g0
                new_inv_sage = new_candidate_sage ** -1
                if not any([self._is_in_order(new_inv_sage * old) for old in reps]):
                    reps.append(new_candidate_sage)
        else:
            reps = [self.B([l,i,0,1]) for i in range(l)] + [self.B([1,0,0,l])]
        return reps

    def get_hecke_ti(self,gk1,gamma,l):
        elt = gk1**-1 * gamma
        for gk2 in self.get_hecke_reps(l):
            ti = elt * gk2
            if all([o.denominator().valuation(l) == 0 for o in self._quaternion_to_list(ti)]):
                return self(ti)
        assert 0


    r'''
    Given two vertices (or edges if as_edges == True), return an element `g`
    of ArithGroupElement such that `g\cdot``v1`` = ``v2``.
    '''
    def are_equivalent(self,v1,v2,as_edges = False):
        raise NotImplementedError

    def gen(self,i):
        if self.discriminant == 1 and self.level != 1:
            return None #raise NotImplementedError
        return self._gens[i]

    def gens(self):
        if self.discriminant == 1 and self.level != 1:
            raise NotImplementedError
        return self._gens

    def element_from_vector(self,x):
        return prod([g**n for g,n in zip(self.gens(),x)])

    r'''
    EXAMPLES:

    sage: G = ArithGroup(6,1)
    sage: Gab,phi = G.abelianization()
    sage: print phi(G.gen(0)*G.gen(1)^2*G.gen(2)) == phi(G.gen(0))+2*phi(G.gen(1))+phi(G.gen(2))
    True
    '''
    def abelianization(self):
        if self.discriminant != 1:
            V = ZZ^len(self.gens())
            W = V.span([sum(a*v for a,v in zip(V.gens(),rel)) for rel in self.get_relation_matrix().rows()])
            Gab = V/W
            return Gab,V #self.hom([Gab(o) for o in V.gens()],codomain = Gab)
        else:
            self.modsym_ambient = ModularSymbols(self.level,sign = 1)
            self.modsym_cuspidal = self.modsym_ambient.cuspidal_subspace()[0]
            self.modsym_map = self.modsym_cuspidal.projection()
            ngens = self.modsym_cuspidal.dimension()
            V = ZZ^ngens
            W = V.span([])
            return V/W,V

class ArithGroupElement(MultiplicativeGroupElement):
    r'''
    INPUT:  a list of the form [(g1,a1),(g2,a2),...,(gn,an)] where the gi are indices
            refering to fixed generators, and the ai are integers, or
            an element of the quaternion algebra ``self.parent().quaternion_algebra()``
    '''
    def __init__(self,parent, word_rep = None, quaternion_rep = None, check = False):
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
                rednrm = quaternion_rep.reduced_norm() if self.parent().discriminant != 1 else quaternion_rep.determinant()
                if rednrm != 1:
                    print quaternion_rep
                    raise ValueError,'Quaternion must be of norm 1'
            if check and not parent._is_in_order(quaternion_rep):
                    print quaternion_rep
                    raise ValueError,'Quaternion must be in Order'
            self.quaternion_rep = quaternion_rep
            set_immutable(self.quaternion_rep)
            self.has_quaternion_rep = True
            # self.word_rep = self._word_rep() # debug
            init_data = True
        if init_data is False:
            raise ValueError,'Must pass either quaternion_rep or word_rep'
        self._reduce_word(check = check)

    def _repr_(self):
        return str(self.quaternion_rep)

    def _mul_(left,right):
        word_rep = None
        quaternion_rep = None
        if left.has_word_rep and right.has_word_rep:
            word_rep = left.word_rep + right.word_rep
        if (left.has_quaternion_rep and right.has_quaternion_rep) or word_rep is None:
            quaternion_rep = left.quaternion_rep * right.quaternion_rep
        return ArithGroupElement(left.parent(),word_rep = word_rep, quaternion_rep = quaternion_rep, check = False)

    def is_one(self):
        quatrep = self.quaternion_rep
        return quatrep == 1

    def __invert__(self):
        word_rep = None
        quaternion_rep = None
        if self.has_word_rep:
            word_rep = [(g,-i) for g,i in reversed(self.word_rep)]
        if self.has_quaternion_rep:
            quaternion_rep = self.quaternion_rep**(-1)
        return ArithGroupElement(self.parent(),word_rep = word_rep, quaternion_rep = quaternion_rep, check = False)

    def __cmp__(self,right):
        selfquatrep = self.quaternion_rep
        rightquatrep = right.quaternion_rep
        return selfquatrep.__cmp__(rightquatrep)

    def _reduce_word(self, check = False):
        if not self.has_word_rep:
            return
        if check:
            self.check_consistency(txt = '1')
        self.word_rep = reduce_word(self.word_rep)
        if check:
            self.check_consistency(txt = '2')

    r'''
    Returns a word in the generators of `\Gamma` representing the given quaternion `x`.
    '''
    @lazy_attribute
    def word_rep(self):
        tmp = self.parent().get_word_rep(self.quaternion_rep)
        self.has_word_rep = True
        self.check_consistency(self.quaternion_rep,tmp,txt = '3')
        return tmp

    r'''
    Returns the quaternion representation.
    '''
    @lazy_attribute
    def quaternion_rep(self):
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

    r'''
   Returns the nth letter of the form g^a
    '''
    def __getitem__(self,n):
        g,a = self.word_rep[n]
        return self.parent().gen(g)**a

    def is_trivial_in_abelianization(self):
        return self.get_weight_vector() in self.parent().get_relation_matrix().image()
        # try:
        #     return self.get_weight_vector() in self.parent().get_relation_matrix().image()
        # except RuntimeError:
        #     return False

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

    r'''
    Returns a list [(g1,h1),(g2,h2),...,(gn,hn)]
    where the gi and the hi are indices of the generators of self.parent()

    TESTS:
    sage: G = BigArithGroup(5,6,1)
    sage: a = G([(1,2),(0,3),(2,-1)])
    sage: b = G([(1,3),(2,-1),(0,2)])
    sage: c= a^2*b^-1
    sage: rel_words = G.Gn.get_relation_words()
    sage: x = commutator(a,b)*G(rel_words()[0])*commutator(c,b)*G(rel_words()[3])^-3*commutator(a*b,c)*commutator(b,a)*G(rel_words()[2])^5*commutator(a*b,c*a)
    sage: v = x.decompose_into_commutators()
    sage: print prod(v) == x
    True
    '''
    def decompose_into_commutators(self):
        oldword = self._calculate_weight_zero_word()
        G = self.parent()

        # At this point oldword has weight vector 0
        # We use the identity:
        # C W0 g^a W1 = C [W0,g^a] g^a W0 W1
        commutator_list = []
        for i in range(len(G.gens())):
            while True:
                # Find the first occurence of generator i
                try:
                    idx = [x[0] for x in oldword[1:]].index(i) + 1
                except ValueError:
                    break
                w0 = ArithGroupElement(G,word_rep = oldword[:idx])
                gatmp = [oldword[idx]]
                ga = ArithGroupElement(G,word_rep = gatmp)
                oldword = reduce_word(gatmp + oldword[:idx] + oldword[idx+1:])
                commutator_list.append(commutator(w0,ga))
        assert len(oldword) == 0
        return commutator_list

r'''
We define [x,y] = x y x^-1 y^-1
'''
class ArithGroupCommutator(ArithGroupElement):
    def __init__(self,parent, x, y):
        # Need to ensure that x and y are ArithGroupElements
        if not (isinstance(x, ArithGroupElement) and isinstance(y,ArithGroupElement)):
            raise TypeError,'x and y must be of type ArithGroupElement'
        self.left = ArithGroupElement(parent,word_rep = x.word_rep, quaternion_rep = x.quaternion_rep, check = True)
        self.right = ArithGroupElement(parent,word_rep = y.word_rep, quaternion_rep = y.quaternion_rep, check = True)
        new_elt = x*y*x^(-1)*y^(-1)
        ArithGroupElement.__init__(self,parent,word_rep = new_elt.word_rep, quaternion_rep = new_elt.quaternion_rep, check = True)

    def _repr_(self):
        return 'Commutator '+ ArithGroupElement._repr_(self)


######################
##                  ##
##    COHOMOLOGY    ##
##                  ##
######################

class Cohomology(Parent):
    def __init__(self,G,V):
        self._group = G
        self._coeffmodule = V
        self._Ga,self._V = G.abelianization()
        self._free_idx = []
        for i in range(len(self._Ga.invariants())):
            if self._Ga.invariants()[i] == 0:
                self._free_idx.append(i)
        self._num_abgens = len(self._free_idx)
        self._F = QQ^self._num_abgens
        self._space = Hom(self._F,V)
        Parent.__init__(self)

    def _an_element_(self):
        return CohomologyClass(self,matrix(QQ,self._F.dimension(),self._coeffmodule.dimension,range(len(self._num_abgens))))

    def _element_constructor_(self,data):
        return CohomologyClass(self,data)

    def _coerce_map_from_(self,S):
        if isinstance(S,Cohomology):
            return True
        else:
            return False

    def _group_element_to_abelianized(self,g):
        v = self.phi(g)
        return self._F([v[i] for i in self._free_idx])

    def _abelianized_vector_to_group_element(self,v):
        G = self.group()
        indices_vec = [self._Ga.gen(o).lift() for o in self._free_idx]
        return prod([G.gen(idx)**n for indices in indices_vec for idx,n in zip(indices,v)],G(1))

    def group(self):
        return self._group

    def _repr_(self):
        return 'H^1(G,V), with G being %s and V = %s'%(self.group(),self.coefficient_module())

    r''' Given an element x in Gamma, returns its image in the abelianized group'''
    def phi(self, x):
        Gab = self._Ga
        if self._group.discriminant != 1:
            V = self._V
            return Gab(sum([ZZ(a)*Gab(V.gen(g)) for g,a in x.word_rep]))
        else:
            M = self.group().modsym_ambient
            f = self.group().modsym_map
            M1 = self.group().modsym_cuspidal
            a,b,c,d = x.quaternion_rep.list()
            tmp = Gab(M1.coordinate_vector(4*f(M([Cusps(Infinity),M2Z(x.quaternion_rep) * Cusps(Infinity)]))))
            return tmp

    def coefficient_module(self):
        return self._coeffmodule

    def basis(self):
        return self._space.basis()

    def dimension(self):
        return len(self.basis())

    def gen(self,i):
        return CohomologyClass(self,self.basis()[i])

    def gens(self):
        return [CohomologyClass(self,f) for f in self.basis()]

    @cached_method
    def hecke_matrix(self,l):
        if self._group.discriminant == 1:
            raise NotImplementedError
        if self.coefficient_module().dimension() != 1:
            raise NotImplementedError
        hecke_reps = self.group().get_hecke_reps(l)
        emb = self.group().get_embedding(20)
        H = self._space
        Gpn = self.group()
        dim = self.dimension()
        M = matrix(QQ,dim,dim,0)
        for j,c in enumerate(H.basis()):
            # Construct column j of the matrix
            for i in range(dim):
                gamma = prod([Gpn.gen(idx)**a for idx,a in zip(range(len(Gpn.gens())),list(self._Ga.gen(self._free_idx[i]).lift()))]).quaternion_rep
                M[i,j] = sum([c(self._group_element_to_abelianized(Gpn.get_hecke_ti(gk1,gamma,l))) for gk1 in hecke_reps])[0]
        return M

    @cached_method
    def involution_at_infinity_matrix(self):
        if self.coefficient_module().dimension() != 1:
            raise NotImplementedError

        emb = self.group().get_embedding(20)
        H = self._space
        Gpn = self.group()

        Obasis = Gpn.Obasis
        for V in product(range(-5,6),repeat = len(Obasis)):
            x = sum([v*o for v,o in zip(V,Obasis)])
            rednrm = x.reduced_norm() if self.group().discriminant != 1 else x.determinant()
            if rednrm == -1:
                found = True
                break
        assert found
        dim = self.dimension()
        M = matrix(QQ,dim,dim,0)
        for j in range(dim):
            c = H.basis()[j]
            # Construct column j of the matrix
            for i in range(dim):
                ti = x**-1 * prod([Gpn.gen(idx)**a for idx,a in zip(range(len(Gpn.gens())),list(self._Ga.gen(self._free_idx[i]).lift()))]).quaternion_rep * x
                tmp = Gpn(ti)
                M[i,j] = c(self._group_element_to_abelianized(tmp))[0]
        return M

r'''
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
class CohomologyClass(ModuleElement):
    r'''
    Define an element of `H^1(G,V)`

    INPUT:
        - G: a BigArithGroup
        - V: a CoeffModule
        - data: a list
    '''
    def __init__(self, parent, data):
        G = parent.group()
        if isinstance(data,list) and parent.coefficient_module().dimension() == 1:
            data = matrix(QQ,parent.dimension(),1,data)
        self._val = parent._space(data)
        ModuleElement.__init__(self,parent)

    def _repr_(self):
        return 'Cohomology class %s'%self._val

    def  _add_(self,right):
        assert self.parent() is right.parent()
        return CohomologyClass(self.parent(),self._val + right._val)

    def __call__(self,gamma):
        return HarmonicCocycle(self.parent(),self._val,gamma)

class HarmonicCocycle(SageObject):
    def __init__(self,H,morphism,gamma,twist = 1):
        self.H = H
        self.gamma = gamma
        self.morphism = morphism
        self.twist = twist

    @cached_method
    def __call__(self,h):
        sign, edge = h
        H = self.H
        Gpn = H.group()

        if self.twist != 1:
            assert 0
            b = Gpn.reduce_in_amalgam(edge * self.twist)
            a = Gpn.reduce_in_amalgam(b**-1 * edge * self.twist * self.gamma)
        else:
            a = Gpn.reduce_in_amalgam(edge * self.gamma)

        elt = H._group_element_to_abelianized(Gpn(a))
        return sign * self.morphism(elt.list())

    def act_by(self,g):
        return HarmonicCocycle(self.H,self.morphism,self.gamma,twist = g)

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

    def _repr_(self):
        return 'Group of divisors on Hp, over ' + self._field._repr_()


class DivisorOnHp(ModuleElement):
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
    def __init__(self,parent,data):
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
        return DivisorOnHp(self.parent(),dict(((a*P+b)/(c*P+d),-n) for P,n in self._data.iteritems()))


    @cached_method
    def degree(self):
        return sum(self._data.itervalues())

    @cached_method
    def size(self):
        return sum([ZZ(d).abs() for d in self._data.itervalues()])

    def support(self):
        return Set([d for d in self._data])

class Homology(Parent):
    r'''

    INPUT:
    - G: a BigArithGroup
    - V: a CoeffModule
    '''
    def __init__(self,G,V):
        self._group = G
        self._coeffmodule = V
        Parent.__init__(self)
        V._unset_coercions_used()
        V.register_action(ArithGroupAction(G.Gn,V))
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
    sage: xi2 = xi.zero_degree_equivalent_through_commutators()
    '''
    def __init__(self, parent, data):
        if not isinstance(data,dict):
            raise ValueError,'data should be a dictionary indexed by elements of ArithGroup'
        self._data = copy(data)
        ModuleElement.__init__(self,parent)

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

    r'''
    Use the relations:
    gh|v = g|v + h|g^-1 v
    g^a|v = g|(v + g^-1v + ... + g^-(a-1)v)
    g^(-a)|v = - g^a|g^av
    '''
    def zero_degree_equivalent(self):
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
                    g = G.Gn.gen(i)
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
        newdict = dict()
        for g,v in chain(self._data.iteritems(),right._data.iteritems()):
            try:
                newdict[g] -= v
                if newdict[g].is_zero():
                    del newdict[g]
            except KeyError:
                newdict[g] = v
        return HomologyClass(self.parent(),newdict)

    def act_by_hecke(self,l):
        newdict = dict()
        G = self.parent().group()
        iota = self.parent().group().get_embedding(20) # Watch precision!
        for gk1 in G.Gpn.get_hecke_reps(l):
            for g,v in self._data.iteritems():
                ti = G.Gpn.get_hecke_ti(gk1,g.quaternion_rep,l)
                newv = v.left_act_by_matrix(iota(gk1**-1))
                try:
                    newdict[ti] += newv
                    if newdict[ti].is_zero():
                        del newdict[ti]
                except KeyError:
                    newdict[ti] = newv
        return HomologyClass(self.parent(),newdict)

    def mult_by(self,a):
        return self.__rmul__(a)

    def hecke_smoothen(self,r):
        return self.act_by_hecke(r) - self.mult_by(r+1)

    def __rmul__(self,a):
        if a == 0:
            return HomologyClass(self.parent(),dict([]))
        else:
            return HomologyClass(self.parent(),dict(((g,a*v) for g,v in self._data.iteritems())))

    # def zero_degree_equivalent_through_commutators(self):
    #     newdict = defaultdict(self.parent().coefficient_module())
    #     for oldg,v in self._data.iteritems():
    #         if v.degree() == 0:
    #             newdict[oldg] += v
    #         else:
    #             commutator_list = oldg.decompose_into_commutators()
    #             for commutator in commutator_list:
    #                 g = commutator.left
    #                 h = commutator.right
    #                 gv =  g*v
    #                 hgv = h*gv
    #                 ginv = g^-1
    #                 newdict[ginv] += hgv - gv
    #                 if newdict[ginv].is_zero():
    #                     del newdict[ginv]
    #                 hinv = h^-1
    #                 g1hgv = (ginv)*hgv
    #                 newdict[hinv] += g1hgv - hgv
    #                 if newdict[hinv].is_zero():
    #                     del newdict[hinv]
    #     return HomologyClass(self.parent(),newdict)

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
def integrate_H1(G,cycle,cocycle,depth,cov = None):
    res = 1
    for g,divisor in cycle.get_data():
        # if divisor.degree() != 0:
        #     raise ValueError,'Divisor must be of degree 0'
        fd = lambda t : prod([(t - P)**n for P,n in divisor._data.iteritems()]) if t != Infinity else 1
        tmp = integrate_H0(G,fd,cocycle(g.quaternion_rep),depth,cov)
        res *= tmp
    return res

r'''
Integration pairing of a function with an harmonic cocycle.
'''
def integrate_H0(G,phi,hc,depth,cov = None):
    p = G.p
    prec = max([20,2*depth])
    emb = G.get_embedding(prec)
    res = 1
    if cov is None:
        cov = G.get_covering(depth)
    n_ints = 0
    for e in cov:
        if n_ints % 500 == 499:
            verbose('Done %s percent'%(100*RealField(10)(n_ints)/len(cov)))
        n_ints += 1
        hce = ZZ(hc(e).list()[0])
        if hce == 0:
            continue
        #verbose('hc = %s'%hce)
        te = sample_point(G,e,prec)
        res *= phi(te)**hce
    return res

def sample_point(G,h,prec = 20):
    sign, e = h
    emb = G.get_embedding(prec)
    a,b,c,d = emb(e**-1).list()

    if sign == 1:
        if d == 0:
            return Infinity
        return  b/d
    else:
        if c == 0:
            return Infinity
        return a/c

def measure_test(G,hc,E):
    p = G.p
    prec = 20
    res = 0
    n_ints = 0
    for e in E:
        # if n_ints % 100 == 0:
        #     verbose('Done %s percent'%(100*RealField(10)(n_ints)/len(E)))
        n_ints += 1
        hce = ZZ(hc(e).list()[0])
        print hce
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
        for e1 in G.subdivide([e],1):
            te1 = sample_point(G,e1,prec)
            if te1 == Infinity:
                continue
            assert ((te-tau1)/(te-tau2) - (te1-tau1)/(te1-tau2)).valuation() >= level
