from sage.matrix.all import matrix,Matrix
from itertools import starmap,izip,product,chain
from operator import mul,itemgetter
from functools import wraps
import os.path
import gc,errno,signal,os,types
from util import *
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,Zmod
from sage.groups.generic import discrete_log
from sage.all import prod
from random import shuffle
from sage.arith.all import gcd, divisors

##########################################################################################
# now the new functions that we need...they follow pretty close the article we're writting
##########################################################################################
def factorize_matrix(m,M):
    #assert is_in_Gamma_1(m,M,determinant_condition = False)
    assert m.det().abs() == 1
    a,b,c,d = m.list()
    if QQ(a).denominator() != 1:
        raise RuntimeError
        #return [m]
    assert a % M == 1
    aabs = ZZ(a).abs()
    Zm = Zmod(M)
    for alphamul in sorted(range(-aabs.sqrt(50)/M,aabs.sqrt(50)/M),key = lambda x: ZZ(x).abs()):
        alpha = 1 + M*alphamul
        if alpha.abs() >= aabs:
            continue
        delta0 = (Zm(alpha)**(-1)).lift()
        for delta in xrange(delta0-10*M,delta0+10*M,M):
            if alpha * delta == 1:
                continue
            gamma0 = ZZ( (alpha*delta -1) / M)
            c1vec = divisors(gamma0)
            for c1 in c1vec:
                ulentry = (a*delta-b*c1*M).abs()
                urentry = (b*alpha-a*gamma0/c1).abs()
                if ulentry < aabs and urentry < b.abs():
                    gamma = c1*M
                    beta = ZZ(gamma0/c1)
                    r1 = Matrix(QQ,2,2,[alpha,beta,gamma,delta])
                    r2 = m*r1.adjoint()
                    assert r1.determinant() == 1
                    assert is_in_Gamma_1(r1,M,determinant_condition = False)
                    assert is_in_Gamma_1(r1,M,determinant_condition = False)
                    V1 = factorize_matrix(r1,M)
                    V2 = factorize_matrix(r2,M)
                    return V2 + V1
    return [m]

#given a matrix M=[a,b,c,d] we run over all lambda in O until we find some satisfying that the class of c mod a+lambda*c is represented by a unit; observe that we are not requiring that a+lambda*c is a prime, nor that the units generate all the quotient ring: if the class of c (mod a+lambda*c) can be represented by a unit, that's fine
#Rmk: maybe here's room for improvement: the loop is pretty pedestrian, and moreover it's not clear at all that we're running over the best lambda'a possible...but apparently it works so far...
#adapted
def find_lambda(M,p,n_results = 1):
    a,b,c,d=M.list()
    if c == 0:
        return [(0,a)]
    valc = c.valuation(p)
    vala = a.valuation(p)
    ap = ZZ(p**(-vala)*a)
    cp = ZZ(p**(-valc)*c)

    lmbd0 = ZZ(QQ(-ap/cp).round())
    lambda_set = sorted([(ZZ(lmbd0 + delta),ZZ(ap+(lmbd0 + delta)*cp)) for delta in range(-20,+20)],key = lambda x:x[1].abs())
    res = []
    for lmd,aplc in lambda_set:
        res.extend([(lmd*p**(vala-valc),unit*p**(valc)) for unit in is_represented_by_unit(aplc,cp,p)])
        if len(res) >= n_results:
            return res[:n_results]
    if len(res) == 0:
        verbose('Lambda not found')
        raise RuntimeError,'Lambda not found'
    return res[:n_results]

#we want to know if the class of c mod a is represented by a unit in F
#returns the unit representing c mod a if it is, and returns False otherwise
#adapted
def is_represented_by_unit(a,c,p):
    #we can forget about powers of p, because they are units; then we can work with integers
    vala = 0
    valc = 0
    while a % p == 0:
        vala += 1
        a = ZZ(a/p)
    while c % p == 0:
        valc += 1
        c = ZZ(c/p)
    aa = a.abs()
    # verbose('is_rep_by_unit aa=%s, cc=%s'%(aa,cc_mod_aa))
    G = Zmod(aa)
    cc = G(c)
    Gp = G(p)
    res = []
    sizeG = G.unit_group_order()
    expn = G.unit_group_exponent()
    # verbose('Group of order=%s'%sizeG)
    try:
        n0 = discrete_log(cc,Gp,sizeG,operation = '*')
        n0 = n0 % expn
        if n0 > expn/2:
            n0 -= expn
        res.append( p**ZZ(n0 + valc) )
    except (ValueError,RuntimeError): pass
    try:
        n0 = discrete_log(cc,-Gp,sizeG,operation = '*')
        n0 = n0 % expn
        if n0 > expn/2:
            n0 -= expn
        res.append( (-1)**n0 * p**ZZ(n0 + valc) )
    except (ValueError,RuntimeError): pass
    return res

def num_evals(tau1,tau2):
    p = tau1.parent().prime()
    dr1 = find_containing_affinoid(p,tau1).determinant().valuation(p)
    dr2 = find_containing_affinoid(p,tau2).determinant().valuation(p)
    delta = find_center(p,1,tau1,tau2).determinant().valuation(p)
    distance = dr1+dr2-2*delta
    return p + 1  + (p-1) * distance


def compute_tau0(v0,gamma,wD,return_exact = False):
    r'''
    INPUT:

     - v0: F -> its localization at p
     - gamma: the image of wD (the generator for an order of F) under an optimal embedding

    OUTPUT:

     The element tau_0 such that gamma * [tau_0,1] = wD * [tau_0,1]

    '''
    R = PolynomialRing(QQ,names = 'X')
    X = R.gen()
    F = v0.domain()
    Cp = v0.codomain()
    assert wD.minpoly() == gamma.minpoly()
    a,b,c,d = gamma.list()
    tau0_vec = (c*X**2+(d-a)*X-b).roots(F)
    tau0 = v0(tau0_vec[0][0])
    idx = 0
    if c * tau0 + d != v0(wD):
        tau0 = v0(tau0_vec[1][0])
        idx = 1
    return tau0_vec[idx][0] if return_exact == True else tau0

def order_and_unit(F,conductor):
    r'''
    Returns an order in F and a fundamental unit in the order.
    It ensures that `u` satisfies (recall that F is real quadratic) that
    `u` belongs to the order `ZZ` + `ZZ[\delta]`, where `\delta`
    is either `\sqrt{D}/2` (if `D = 0 \pmod 4`), or `(1+\sqrt{D})/2`.
    Here D is the discriminant of the order.
    '''
    #we have to square the unit, so that the determinant is 1
    u0 = F.units()[0]**2 # It looks like the square can (sometimes) be removed!
    # if F.real_embeddings()[0](u0) < 0:
    #     u0 = -u0
    # if F.real_embeddings()[0](u0) < 1:
    #     u0 = 1/u0
    D = F.discriminant() * conductor**2
    sqrtD = conductor * F.gen()
    if F.discriminant() % 4 == 0:
        sqrtD *= 2
    assert sqrtD**2 == D
    delta = sqrtD/2 if D % 4 == 0 else (1+sqrtD)/2
    verbose('delta = %s'%delta)
    u = u0
    O_D = F.order(delta)
    assert O_D.discriminant() == D
    i = 1
    while u not in O_D:
        u *= u0
        i += 1
    verbose('fundamental unit = u^%s'%i)
    return O_D,u

def _find_initial_embedding_list(v0,M,W,orientation,OD,u):
    r'''
    .
    '''
    F = v0.domain()
    p = v0.codomain().base_ring().prime()
    emblist = []
    wD = OD.ring_generators()[0]
    u0vec = wD.coordinates_in_terms_of_powers()(u)
    u0vec_inv = wD.coordinates_in_terms_of_powers()(u**-1)
    assert wD.minpoly() == W.minpoly()
    Blist = [ M2Z([1,0,0,1]) ] + [ M2Z([ZZ(M/d1),i,0,d1]) for d1 in ZZ(M).divisors() for i in range(-2*ZZ(QQ(d1/2).ceil()),2*ZZ(QQ(d1/2).ceil()) + 1) ]
    for B in Blist:
        W_M = B * W * B**-1
        if all([x.is_integral() for x in W_M.list()]) and ZZ(W_M[1,0]) % M == 0:
            if orientation is not None:
                for ell,r in ZZ(M).factor():
                    if W_M[0,0] % ell != orientation % ell:
                        Wl = Matrix(ZZ,2,2,[0,-1,ell,0])
                        W_M = Wl**(-1) * W_M * Wl
                assert all([W_M[0,0] % ell == orientation % ell for ell,r in ZZ(M).factor()])
            # Computation of tau_0: it's one of the roots of the minimal polynomial of W.
            tau0 = compute_tau0(v0,W_M,wD,return_exact = True)
            if F.class_number() > 1 and find_containing_affinoid(p,v0(tau0)).determinant().valuation(p) % 2 == 1 and orientation is not None:
                Wp = Matrix(ZZ,2,2,[0,-1,p,0])
                W_M = Wp**(-1) * W_M * Wp
                assert all([W_M[0,0] % ell == orientation % ell for ell,r in ZZ(M).factor()])
                tau0 = compute_tau0(v0, W_M,wD,return_exact = True)
                assert find_containing_affinoid(p,v0(tau0)).determinant().valuation(p) % 2 == 0
            gtau_orig_1 = u0vec[0] + u0vec[1] * W_M
            gtau_orig_2 = u0vec_inv[0] + u0vec_inv[1] * W_M
            emblist.extend([(tau0,gtau_orig_1),(tau0,gtau_orig_2)])
    if len(emblist) == 0:
        raise RuntimeError,'No embeddings found !'
    verbose("Found %s initial embeddings."%len(emblist))
    return emblist

def _explode_embedding_list(v0,M,emblist,power = 1):
    p = v0.codomain().base_ring().prime()
    list_embeddings = []
    for tau0,gtau_orig in emblist:
        gtau = gtau_orig**power
        verbose('gtau = %s'%gtau)
        ## First method
        for u1 in is_represented_by_unit(M,ZZ(gtau[0,0]),p):
            u_M1 = matrix(QQ,2,2,[u1**-1,0,0,u1])
            gtau1 = u_M1 * gtau
            tau01 = tau0 / (u1**2)
            if gtau1[0,0] % M == 1:
                list_embeddings.append((tau01,gtau1,1))
            elif gtau1[0,0] % M == -1:
                list_embeddings.append((tau01,-gtau1,1))
        ## Second method
        if M > 1:
            a_inv = ZZ((1/Zmod(M)(gtau[0,0])).lift())
            for u2 in is_represented_by_unit(M,a_inv,p):
                u_M2 = matrix(QQ,2,2,[u2,0,0,u2**-1])
                gtau2 = u_M2 * gtau
                tau02 = u2**2 * tau0 #act_flt(u_M2,tau0)
                if gtau2[0,0] % M == 1:
                    list_embeddings.append((tau02,gtau2,1))
                elif gtau1[0,0] % M == -1:
                    list_embeddings.append((tau02,-gtau2,1))
    verbose('Found %s embeddings...'%len(list_embeddings))
    return list_embeddings

def find_tau0_and_gtau(v0,M,W,orientation = None,extra_conductor = 1,algorithm = 'guitart_masdeu'):
    F = v0.domain()
    r = F.gen()
    Cp = v0.codomain()
    p = Cp.base_ring().prime()
    if F.degree() != 2 or len(F.ideal(p).factor()) > 1 or gcd(p,F.disc()) !=1:
        raise ValueError,'Not a valid field'
    w=F.maximal_order().ring_generators()[0]
    assert w.minpoly() == W.minpoly()
    OD,u = order_and_unit(F,extra_conductor)
    wD = OD.ring_generators()[0]
    wDvec = w.coordinates_in_terms_of_powers()(wD)
    WD = wDvec[0] + wDvec[1]*W
    assert all([o.is_integral() for o in WD.list()])
    assert WD.minpoly() == wD.minpoly()
    #assert F.real_embeddings()[0](u) > 1
    if algorithm == 'darmon_pollack':
        if M != 1:
            raise ValueError,'the level (=%s) must be =1'%M
        u0vec = wD.coordinates_in_terms_of_powers()(u) # Finds a,b such that u = a + b w
        gtau = u0vec[0]+u0vec[1]*WD
        tau0 = compute_tau0(v0,WD,wD)
        return tau0,gtau,1,find_limits(tau0,gtau,1)
    elif algorithm == 'guitart_masdeu':
        # We seek for an optimal embedding of conductor M
        emblist = [emb for sgn in [+1,-1] for emb in _find_initial_embedding_list(v0,M,WD,orientation,OD,sgn * u)]
        print 'Before exploding, have %s embeddings'%len(emblist)
        power = 0
        list_embeddings = []
        while len(list_embeddings) == 0:
            power += 1
            list_embeddings = _explode_embedding_list(v0,M,emblist,power = power)

        print 'We have now %s embeddings'%len(list_embeddings)
        # Now choose the best
        opt_evals = None
        opt_tau = None
        num_emb = 0
        for tau,gtau,sign in list_embeddings:
            # verbose('Analyzing embedding %s...'%num_emb)
            print 'Analyzing embedding %s. Press C-c C-c to skip.'%num_emb
            num_emb += 1
            assert tau.parent().is_exact()
            #if not is_in_Gamma_1(gtau,M,p,determinant_condition = False):
            #    continue
            try: V = find_limits(tau,gtau,M,v0,method = 2)
            except KeyboardInterrupt:
                print 'Key press detected. Continuing.'
                continue
            except RuntimeError:
                print 'Not suitable. Continuing.'
                continue
            if V is None: continue
            n_evals = sum((num_evals(t1,t2) for t1,t2 in V))
            verbose('opt_evals = %s'%opt_evals)
            if opt_evals is None or n_evals < opt_evals:
                opt_evals,opt_tau,opt_gtau,opt_sign,opt_V = n_evals,tau,gtau,sign,V
            if opt_evals is not None and opt_evals < 5 * (p+1)*p**2: # FIXME
                break
        if opt_tau is None:
            raise RuntimeError,'No embedding found'
        verbose('The optimal number of evaluations found is %s'%opt_evals)
        return opt_tau,opt_gtau,opt_sign,opt_V
    else:
        raise ValueError, 'Algorithm must be either "guitart_masdeu" or "darmon_pollack"'

def find_optimal_embeddings(F,use_magma = False,extra_conductor = 1,magma = None):
    w=F.maximal_order().ring_generators()[0]
    D = F.discriminant()
    ## this matrix gives an optimal embedding of conductor 1
    if use_magma == True or extra_conductor != 1:
        if magma is None:
            from sage.interfaces.magma import magma
        tmp = magma.ReducedForms(str(D*extra_conductor**2),nvals = 1)
        G = [[tmp[i+1][j]._sage_() for j in [1,2,3]] for i in range(len(tmp))]
    elif F.class_number() == 1:
        assert extra_conductor == 1
        return [Matrix(QQ,2,2,[w.trace(),-w.norm(),1,0])]
    else:
        assert extra_conductor == 1
        fact = F(1) if D > 0 else w - 1/2 * w.trace()
        G = []
        for I in [F.ideal(cl.gens()) for cl in F.class_group()]:
            alpha,beta = I.integral_basis()
            if QQ((alpha*beta.conjugate() - beta*alpha.conjugate())/fact) < 0:
                alpha,beta = beta,alpha
            nrm = I.norm()
            a = ZZ(alpha.norm()/nrm)
            c = ZZ(beta.norm()/nrm)
            b = ZZ((alpha+beta).norm()/nrm) - a - c
            G.append((a,b,c))
    delta = extra_conductor * F.gen() if D%4 == 1 else 2*extra_conductor * F.gen() # delta = sqrt{discriminant}
    r,s = delta.coordinates_in_terms_of_powers()(w) # w = r + s*delta
    return [Matrix(QQ,2,2,[r-s*B,-2*s*C,2*s*A,r+s*B]) for A,B,C in G] # There's a typo in Darmon-Pollack pg.12, fixed by Juan Restrepo

def _find_limits_manin_trick(tau,gtau):
    if gtau[0,0] == 0:
        return [(1-1/tau,tau-1)]
    else:
       a,c,b,d = gtau.list()
       if b < 0: a,b,c,d = -a,-b,-c,-d
       if b == 0: return []
       if b == 1:
           return _find_limits_manin_trick(tau-a/b,M2Z([0,-1,1,0]))
       else:
           d = (1/(Zmod(b)(a))).lift()
           if 2*d > b : d -= b
           c = ZZ((a*d-1)/b)
           if d < 0:
               a,b,c,d = -a,-b,-c,-d
           return _find_limits_manin_trick((b*tau-a)/(d*tau-c),M2Z([0,-1,1,0])) + _find_limits_manin_trick(tau,M2Z([-c,a,-d,b]))

def _find_limits_prefactoring(tau,gtau,level,v0):
    if tau.parent().is_exact():
        p = v0.codomain().prime()
    else:
        p = tau.parent().prime()
    verbose('Factorizing matrix %s'%gtau.list())
    factorization = factorize_matrix(gtau,level)
    verbose('Done! Used %s matrices.'%len(factorization))
    decomp = []
    for vv in factorization:
        lmb,uu = find_lambda(vv,p,n_results = 1)[0]
        decomp.extend(decompose(vv,lmb,uu))
    assert prod(decomp) == gtau
    if not all((is_in_Gamma_1(mat,level,p,determinant_condition = False) for mat in decomp)):
        for mat in decomp:
            if not is_in_Gamma_1(mat,level,p,determinant_condition = False):
                print mat.list()
                raise RuntimeError
    if any((get_limits_from_decomp(tau,[mat],v0)[1] > p*(p+1) for mat in decomp)):
        raise RuntimeError
    V, n_evals = get_limits_from_decomp(tau,decomp,v0)
    return V

def _find_limits_original(tau,gtau,level,v0):
    if tau.parent().is_exact():
        p = v0.codomain().prime()
    else:
        p = tau.parent().prime()
    opt_evals = None
    opt_V = None
    for lmb,uu in find_lambda(gtau,p,n_results = 1):
        #verbose('trying lambda = %s, u = (-)p^%s'%(lmb,uu.valuation(p)))
        dec = decompose(gtau,lmb,uu)
        assert prod(dec) == gtau
        V,n_evals = get_limits_from_decomp(tau,dec,v0)
        # verbose('n_evals = %s'%n_evals)
        if opt_evals is None or n_evals < opt_evals:
            opt_V = V
            opt_evals = n_evals
    return opt_V

def find_limits(tau,gtau = None,level = 1,v0 = None,method = 1):
    if gtau is None: return []
    if gtau.determinant() == 0:
        raise ValueError,'gtau must have nonzero determinant.'

    if level == 1: # Use Manin trick
        return _find_limits_manin_trick(tau,gtau)
    else:
        if method == 1:
            # Original method, only 5 matrices but possible very ill-conditioned
            return _find_limits_original(tau,gtau,level,v0)
        else:
            assert method == 2
            # Factors the given matrix before doing the 5-step factorization.
            return _find_limits_prefactoring(tau,gtau,level,v0)

def decompose(gtau,lmb,uu):
    if uu == 0:
        return [gtau]
    E_lambda = Matrix(QQ,2,2,[1,lmb,0,1])
    #we know that E_lambda*gtau is a matrix [a,b,c,d] such that c=uu+ta for some unit uu; now we find uu and t
    MM=(E_lambda*gtau).change_ring(QQ)
    a,b,c,d=MM.list()
    t = QQ(c-uu)/QQ(a)
    E1i=Matrix(QQ,2,2,[1,0,uu*(1-a),1])
    E2i=Matrix(QQ,2,2,[1,-1/uu,0,1])
    E34i=Matrix(QQ,2,2,[1,0,c+t*(1-a),1])
    E_x=(E34i*E2i*E1i)**(-1)*MM
    return [E_lambda**(-1), E34i,E2i,E1i,E_x]

def get_limits_from_decomp(tau,decomp,v0):
    oldTau = tau
    V = []
    n_evals = 0
    for mat in decomp:
        a,b,c,d = (mat**-1).list()
        assert oldTau.parent().is_exact()
        newTau = (a*oldTau+b)/(c*oldTau+d)
        if c != 0: # lower-triangular
            assert b == 0
            t1,t2 = v0(oldTau),v0(newTau)
            V.append([t1,t2])
            n_evals += num_evals(t1,t2)
        oldTau = newTau
    return V,n_evals
