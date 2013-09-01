from itertools import product,chain,izip,groupby,islice,tee,starmap
from sage.rings.all import ZZ,QQ,algdep,kronecker_symbol,Qp,RR
from sage.matrix.all import matrix,Matrix
from sage.modular.modform.constructor import EisensteinForms, CuspForms
from sage.schemes.elliptic_curves.constructor import EllipticCurve
from sage.libs.pari.gen import PariError
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.misc.misc import verbose,get_verbose,set_verbose
from sage.calculus.var import var
from sage.interfaces.gp import gp
from sage.libs.pari.gen import pari

def M2Z(v):
    return Matrix(ZZ,2,2,v)

def is_in_principal_affinoid(p,z):
    if z.valuation() != 0:
        return False
    for i in range(p):
        if (z-z.parent()(i)).valuation() > 0:
            return False
    return True

def find_containing_affinoid(p,z,level = 1):
    r"""
    Returns the vertex corresponding to the affinoid in 
    the `p`-adic upper half plane that a given (unramified!) point reduces to.

    INPUT:

      - ``z`` - an element of an unramified extension of `\QQ_p` that is not contained
        in `\QQ_p`.

    OUTPUT:

      A 2x2 integer matrix representing the affinoid.

        sage: K.<a> = Qq(5^2,20)
        sage: find_containing_affinoid(5,a)
        [1 0]
        [0 1]
        sage: z = 5*a+3
        sage: v = find_containing_affinoid(5,z).inverse(); v
        [ 1/5 -3/5]
        [   0    1]

    Note that the translate of ``z`` belongs to the standard affinoid. That is,
    it is a `p`-adic unit and its reduction modulo `p` is not in `\FF_p`::

        sage: a,b,c,d = v.list()
        sage: gz = (a*z+b)/(c*z+d); gz
        a + O(5^19)
        sage: gz.valuation() == 0
        True
    """
    #Assume z belongs to some extension of QQp.
    if(z.valuation(p)<0):
        return M2Z([0,1,p*level,0])*find_containing_affinoid(p,1/(p*z))
    a=0
    pn=1
    val=z.valuation(p)
    L=[0]*val+z.unit_part().list()
    for n in range(len(L)):
        if L[n] != 0:
            if len(L[n]) > 1:
                break
            if len(L[n]) > 0:
                a += pn*L[n][0]
        pn*=p
    return M2Z([pn,a,0,1])

def find_center(p,level,t1,t2):
    r"""
    This function computes the center between two points in Cp
    """
    old_dir = M2Z([1,0,0,1])
    E0inf = [M2Z([0,-1,level,0])]
    E0Zp = [M2Z([p,a,0,1]) for a in range(p)]
    while True:
        new_dirs = [old_dir * e0 for e0 in E0Zp]
        same_ball = False
        new_dir = None
        for g in new_dirs:
            a,b,c,d = (g**(-1)).list()
            # Check whether t1 and t2 are in the open given by g
            if all([(a*t + b).valuation() >= (c*t + d).valuation() for t in [t1,t2]]):
                new_dir = g
                break
        if new_dir is None:
            return old_dir
        else:
            old_dir = new_dir

def is_in_Gamma_1(mat,N,p):
    if N != 1:
        a,b,c,d=mat.list()
        if not all([QQ(x).is_S_integral([p]) for x in [a,b,c,d]]):
            return False
        if Zmod(N)(a) != 1 or Zmod(N)(c) % N != 0:
            return False
    if mat.det() != 1:
        return False
    return True


def is_in_Gamma0loc(A,det_condition = True):
    r'''
    Whether the matrix A has all entries Zp-integral, and is upper-triangular mod p.
    '''
    if det_condition == True and A.determinant() != 1:
        return False
    return all((o.valuation() >= 0 for o in A.list())) and A[1,0].valuation() > 0

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

def set_immutable(x):
    try:
        x.set_immutable()
        return x
    except AttributeError:
        return x

def act_flt(g,x):
    a,b,c,d = g.list()
    return (a*x + b)/(c*x + d)

def tate_parameter(E,R):
    p = R.prime()
    prec = R.precision_cap()
    jE = E.j_invariant()

    # Calculate the Tate parameter
    E4 = EisensteinForms(weight=4).basis()[0]
    Delta = CuspForms(weight=12).basis()[0]
    j = (E4.q_expansion(prec+7))**3/Delta.q_expansion(prec+7)
    qE =  (1/j).power_series().reversion()(R(1/jE))
    return qE

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

    if un == 1:
        return 0,Infinity

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
    C2 = (Eq.c4() * R(E.c6())) / (Eq.c6() * R(E.c4()))
    C = our_sqrt(R(C2),R) #.square_root()
    s = (C - R(E.a1()))/R(2)
    r = (s*(C-s) - R(E.a2())) / 3
    t =  (r*(2*s-C)-R(E.a3())) / 2
    return  ( r + C2 * xx, t + s * C2 * xx + C * C2 * yy )


def period_from_coords(R,E, P, prec = 20,K_to_Cp = None):
    r"""
    Given a point `P` in the formal group of the elliptic curve `E` with split multiplicative reduction,
    this produces an element `u` in `\QQ_p^{\times}` mapped to the point `P` by the Tate parametrisation.
    The algorithm return the unique such element in `1+p\ZZ_p`.

    INPUT:

    - ``P`` - a point on the elliptic curve.

    - ``prec`` - the `p`-adic precision, default is 20.

    """
    # if R is None:
    #     R = u.parent()
    #     u = R(u)
    # p = R.prime()

    #R = Qp(p,prec)
    p = R.prime()

    jE = E.j_invariant()

    if K_to_Cp is None:
        K_to_Cp = lambda x:x

    # Calculate the Tate parameter
    E4 = EisensteinForms(weight=4).basis()[0]
    Delta = CuspForms(weight=12).basis()[0]
    j = (E4.q_expansion(prec+7))**3/Delta.q_expansion(prec+7)
    qE =  (1/j).power_series().reversion()(R(1/jE))
    sk = lambda q,k,pprec: sum( [n**k*q**n/(1-q**n) for n in range(1,pprec+1)] )
    n = qE.valuation()
    precp = ((prec+4)/n).floor() + 2;
    tate_a4 = -5  * sk(qE,3,precp)
    tate_a6 = (tate_a4 - 7 * sk(qE,5,precp) )/12
    Eq = EllipticCurve([R(1),R(0),R(0),tate_a4,tate_a6])

    C2 = (Eq.c4() * R(E.c6())) / (Eq.c6() * R(E.c4()))
    C = our_sqrt(R(C2),R) #.square_root()
    s = (C * R(E.a1()) -R(1))/R(2)
    r = (C**2*R(E.a2()) +s +s**2)/R(3)
    t = (C**3*R(E.a3()) - r)/R(2)
    xx = r + C**2 * K_to_Cp(P[0])
    yy = t + s * C**2 * K_to_Cp(P[0]) + C**3 * K_to_Cp(P[1])
    try:
        EqCp = Eq.change_ring(yy.parent())
        Pq = EqCp([xx,yy])
    except TypeError:
        raise RuntimeError, "Bug : Point %s does not lie on the curve "%[xx,yy]
    tt = -xx/yy
    if tt.valuation(p) <= 0:
        raise  ValueError , "The point must lie in the formal group."

    eqhat = Eq.formal()
    eqlog = eqhat.log(prec + 3)
    z = eqlog(tt)
    u = ZZ(1)
    fac = ZZ(1)
    for i in range(1,2*prec+1):
        fac = fac * i
        u = u + z**i/fac
    un = u * qE**(-(u.valuation()/qE.valuation()).floor())
    return un


def our_algdep(z,degree,prec = None):
    try: return algdep(z,degree)
    except PariError: pass
    if prec is None:
        prec = z.precision_relative()
    field_deg = z.parent().degree()
    p = z.parent().prime()
    R = PolynomialRing(ZZ,names = 'x')
    x = R.gen()
    n = degree+1
    zval = z.valuation()
    ptozval = p**zval
    z /= ptozval
    assert z.valuation() == 0
    pn = p**prec
    r = 1
    M = matrix(ZZ, n+field_deg, field_deg)
    M[0,-1] = 1 # Encodes 1
    for k in range(1, degree+1):
        r *= z
        for i in range(field_deg):
            M[k,-1-i] = ZZ(r._ntl_rep()[i])
    for i in range(field_deg):
        M[n+i,-1-i] = pn
    verb_lev = get_verbose()
    set_verbose(0)
    tmp = M.left_kernel().matrix().change_ring(ZZ).LLL().row(0)
    set_verbose(verb_lev)
    f = R(list(tmp[:n]))(x/ptozval)
    if f.leading_coefficient() < 0:
        f = -f
    return R(f.denominator() * f)


def lift_padic_splitting(a,b,II0,JJ0,p,prec):
    R = Qp(p,prec)
    #II0,JJ0,_ = Q.modp_splitting_data(p)
    II0 = II0.apply_map(lambda o:R(o.lift()))
    II0[1,1] = -II0[0,0]
    JJ0 = JJ0.apply_map(lambda o:R(o.lift()))
    JJ0[1,1] = -JJ0[0,0]
    oldII = None
    oldJJ = None
    newII = II0
    newJJ = JJ0
    n_iters = 0
    current_prec = -1
    while current_prec < prec: #newII != oldII or newJJ != oldJJ:
        n_iters += 1
        oldII,oldJJ = newII,newJJ
        x1,x2,x3,_ = oldII.list()
        y1,y2,y3,_ = oldJJ.list()
        n = min(o.valuation() for o in [x1**2+x2*x3-a,y1**2+y2*y3-b,2*x1*y1+x2*y3+x3*y2])
        verbose('current_prec = %s'%n)
        x1,x2,x3,_ = [o.lift() for o in oldII.list()]
        y1,y2,y3,_ = [o.lift() for o in oldJJ.list()]
        B = matrix(R,3,6,[2*x1,x3,x2,0,0,0,0,0,0,2*y1,y3,y2,2*y1,y3,y2,2*x1,x3,x2])
        pn = p**n
        A = -matrix(R,3,1,[ZZ((x1**2+x2*x3-a)/pn),ZZ((y1**2+y2*y3-b)/pn),ZZ((2*x1*y1+x2*y3+x3*y2)/pn)])
        delta = B.solve_right(A)
        x1,x2,x3,y1,y2,y3 = delta.list()
        newII = oldII + pn*matrix(R,2,2,[x1,x2,x3,-x1])
        newJJ = oldJJ + pn*matrix(R,2,2,[y1,y2,y3,-y1])
        current_prec = n
        if n_iters > 2 * prec:
            raise RuntimeError,'Hensel iteration does not seem to converge'
    return newII,newJJ

def recognize_point(x,y,E,F,prec = None,HCF = None):
  if HCF is None:
      HCF = F.hilbert_class_field(names = 'r1')
  hF = F.class_number()
  Cp = x.parent()
  s = F.gen()
  w = F.maximal_order().ring_generators()[0]
  #assert w.minpoly()(Cp.gen()) == 0
  QQp = Cp.base_ring()
  p = Cp.prime()
  if prec is None:
      prec = QQp.precision_cap()
  if x == 0 and y == 0:
      candidate_x = 0
  elif (1/x).valuation() > prec and (1/y).valuation() > prec:
      return E.change_ring(HCF)(0),True
  else:
      if hF == 1:
          x1 = (p**(x.valuation())*QQp(ZZ(x._ntl_rep()[0]))).add_bigoh(prec)
          x2 = (p**(x.valuation())*QQp(ZZ(x._ntl_rep()[1]))).add_bigoh(prec)
          try:
              x1 = algdep(x1,1).roots(QQ)[0][0]
              x2 = algdep(x2,1).roots(QQ)[0][0]
          except IndexError:
              return x,False
          candidate_x = x1+x2*w
      else:
          candidate_x = our_algdep(x,2*hF,prec)
          pol_height = sum((RR(o).abs().log() for o in candidate_x.coeffs()))/RR(p).log()
          # if pol_height < .8 * prec: # .8 is quite arbitrary...
          #     return candidate_x,True
          try:
              candidate_x = candidate_x.change_ring(HCF).roots()[0][0]
          except IndexError:
              return candidate_x,False
  try:
      Pt = E.change_ring(HCF).lift_x(candidate_x)
      verbose('Point is in curve: %s'%Pt,level=2)
      return Pt,True
  except ValueError:
      verbose('Point does not appear to lie on curve...',level=2)
      return candidate_x,False

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
    ppow = p if p != 2 else 8
    minval = 1 if p != 2 else 3
    for avec in product(range(ppow),repeat=deg):
        y0 = avec[0]
        for a in avec[1:]:
            y0 = y0*z + a
        if (y0**2-x).valuation() >= minval:
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


def act_flt_in_disc(g,x,P):
    z = (P.conjugate()*x - P)/(x-1)
    a,b,c,d = g.list()
    z1 = (a*z + b)/(c*z + d)
    return (z1 - P)/(z1 - P.conjugate())

def translate_into_twosided_list(V):
    vp,vm = V
    return [None] + vp + list(reversed(vm))

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
    new_word = [(g,a) for g,a in word]
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


def get_heegner_params(p,N,dK):
    if N % p != 0:
        raise ValueError,'p (=%s) must divide conductor (=%s)'%(p,N)
    if kronecker_symbol(dK,p) != -1:
        raise ValueError,'p (=%s) must be inert in K (=Q(sqrt{%s}))'%(p,dK)
    N1 = ZZ(N/p)
    if N1 % p == 0:
        raise ValueError,'p (=%s) must exactly divide the conductor (=%s)'%(p,N)
    DB = 1
    Np = 1
    num_inert_primes = 0
    for ell,r in N1.factor():
        if kronecker_symbol(dK,ell) == -1: # inert
            if r != 1:
                raise ValueError,'The inert prime l = %s divides too much the conductor.'%ell
            num_inert_primes += 1
            DB *= ell
        else:
            Np *= ell**r
    assert N == p * DB * Np
    if num_inert_primes % 2 != 0:
        raise ValueError,'There should an even number of primes different than p which are inert'
    return DB,Np

def fwrite(string, outfile):
    if outfile is None:
        return
    with open(outfile,"a") as fout:
        fout.write(string + '\n')
    return

def module_generators(K):
    x=var('x')
    y=var('y')
    F=K.base_field()
    f=F.polynomial()
    g=K.relative_polynomial()
    a=F.gen()
    b=K.gen()

    # Equivalent pari objects
    FP=F.pari_bnf().subst(x,y)
    fP=pari(f)
    KP=K.pari_rnf()
    gP=KP[0]
    BP=gp.rnfhnfbasis(FP,gP)

    E=[gp.matbasistoalg(FP,BP.vecextract(1)).lift(),gp.matbasistoalg(FP,BP.vecextract(2)).lift()]

    A=Matrix(F,2,2,0)
    for jj in range(2):
        for ii in [1,2]:
            tmp=E[jj][ii,1].Vec().sage()
            if(len(tmp)==2):
                A[ii-1,jj]=tmp[0]*a+tmp[1]
            else:
                A[ii-1,jj]=tmp[0]
    return (Matrix(K,1,2,[1,b])*A).list()

def find_the_unit_of(F,K):
    found=False
    for eps in K.units():
        is_square,root=eps.norm(F).is_square(root=True)
        deg=eps.minpoly().degree()
        if deg==2:
            unit_not_in_F=eps
        if is_square and deg==2:
            return eps/root
    # Not found so far..
    norm=unit_not_in_F.norm(F)
    return unit_not_in_F**2/norm

def conjugate_quaternion_over_base(q):
    v = q.coefficient_tuple()
    B = q.parent()
    F = B.base_ring()
    deg = F.degree()
    if deg == 1:
        return q
    elif deg > 2:
        raise NotImplementedError
    else:
        return B([F(o).trace() - o for o in v])

def sage_F_elt_to_magma(F_magma,x):
    return F_magma(x.list())

def magma_F_elt_to_sage(F_sage,x):
    return F_sage([QQ(x[i+1]) for i in range(F_sage.degree())])

def magma_quaternion_to_sage(B_sage,x):
    tmp = B_sage([magma_F_elt_to_sage(B_sage.base_ring(),x.Vector()[m+1]) for m in range(4)])
    return tmp

def magma_integral_quaternion_to_sage(B_sage,O_magma,F_magma,x):
    F = B_sage.base_ring()
    tmp = []
    xseq = x.ElementToSequence()
    basis = O_magma.Basis()
    return sum(magma_F_elt_to_sage(F,F_magma(xseq[i+1])) * magma_quaternion_to_sage(B_sage,basis[i+1]) for i in range(4))

def sage_quaternion_to_magma(B_magma,x):
    v = list(x.coefficient_tuple())
    return B_magma(sage_F_elt_to_magma(B_magma.BaseRing(),v[0])) + sum(sage_F_elt_to_magma(B_magma.BaseRing(),v[i+1])*B_magma.gen(i+1) for i in range(3))

def sage_F_ideal_to_magma(F_magma,x):
    Zm = F_magma.RingOfIntegers()
    gens = x.gens_two()
    return sage_F_elt_to_magma(F_magma,gens[0])*Zm + sage_F_elt_to_magma(F_magma,gens[1])*Zm

def magma_F_ideal_to_sage(F_sage,x):
    gens = x.TwoElement(nvals = 2)
    return F_sage.ideal([magma_F_elt_to_sage(F_sage,gens[0]),magma_F_elt_to_sage(F_sage,gens[1])])


