######################
##                  ##
##  INTEGRATION     ##
##                  ##
######################
import itertools
from collections import defaultdict
from itertools import product,chain,izip,groupby,islice,tee,starmap
#from distributions import Distributions, Symk
from sigma0 import Sigma0,Sigma0ActionAdjuster
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,LaurentSeriesRing,PowerSeriesRing,lcm, Infinity,Zmod
from sage.all import prod
from operator import mul
from util import *
from limits import num_evals,find_center
from sage.parallel.decorate import fork,parallel
from sage.misc.getusage import get_memory_usage
import os

oo = Infinity

def act_on_polynomial(P,num,den,N = None):
    if N is None:
        N = P.degree()
    R = num.parent()
    ans = R(0)
    numvec = [R(1)]
    denvec = [R(1)]
    for i in range(N):
        numvec.append(num*numvec[-1])
        denvec.append(den*denvec[-1])
    Plist = P.list()
    for i in range(N+1):
        ai = Plist[i]
        ans += ai*numvec[i]*denvec[N-i]
    return ans

def double_integral_zero_infty(Phi,tau1,tau2):
    p = Phi.parent().prime()
    K = tau1.parent()
    R = PolynomialRing(K,'x')
    x = R.gen()
    R1 = PowerSeriesRing(K,'r1')
    r1 = R1.gen()
    R1.set_default_prec(Phi.precision_absolute())
    level = Phi._map._manin.level()
    E0inf = [M2Z([0,-1,level,0])]
    E0Zp = [M2Z([p,a,0,1]) for a in range(p)]

    predicted_evals = num_evals(tau1,tau2)

    a,b,c,d = find_center(p,level,tau1,tau2).list()
    h = M2Z([a,b,c,d])
    E = [h*e0 for e0 in E0Zp + E0inf]

    resadd = 0
    resmul = 1
    total_evals = 0
    percentage = QQ(0)
    ii = 0
    f = (x-tau2)/(x-tau1)
    while len(E) > 0:
        ii += 1
        increment = QQ((100-percentage)/len(E))
        verbose('remaining %s percent (and done %s of %s evaluations)'%(RealField(10)(100-percentage),total_evals,predicted_evals))
        newE = []
        for e in E:
            a,b,c,d = e.list()
            assert ZZ(c) % level == 0
            try:
                y0 = f((a*r1+b)/(c*r1+d))
                val = y0(y0.parent().base_ring()(0))
                if all([xx.valuation(p)>0 for xx in (y0/val - 1).list()]):
                    if total_evals % 100 == 0:
                        Phi._map._codomain.clear_cache()
                    pol = val.log(p_branch = 0)+((y0.derivative()/y0).integral())
                    V = [0] * pol.valuation() + pol.shift(-pol.valuation()).list()

                    try:
                        phimap = Phi._map(M2Z([b,d,a,c]))
                    except OverflowError:
                        print a,b,c,d
                        raise OverflowError,'Matrix too large?'
                    mu_e0 = ZZ(phimap.moment(0).rational_reconstruction())
                    mu_e = [mu_e0] + [phimap.moment(o).lift() for o in range(1,len(V))]
                    resadd += sum(starmap(mul,izip(V,mu_e)))
                    resmul *= val**mu_e0
                    percentage += increment
                    total_evals += 1
                else:
                    newE.extend([e*e0 for e0 in E0Zp])
            except ZeroDivisionError:
                #raise RuntimeError,'Probably not enough working precision...'
                newE.extend([e*e0 for e0 in E0Zp])
        E = newE
    verbose('total evaluations = %s'%total_evals)
    val = resmul.valuation()
    return p**val*K.teichmuller(p**(-val)*resmul)*resadd.exp()

##----------------------------------------------------------------------------
##  double_integral(tau1,tau2,r,s)
##
## Input:
##    tau1,tau2: Elements of the ``standard affinoid" in H_p consisting
##               of elements in PP_1(C_p) whose natural image in
##               P_1(F_p-bar) does not belong to P_1(F_p).
##    r,s:       Elements of P_1(Q). The cusp r=a/b is
##               represented in the form r=[a,b], with a and b relatively
##               prime integers, and b>=0. By convention infty=[1,0].
##    omega:     The modular form on Gamma_0(p), represented as above.
##
## Output:
##    The ``multiplicative double integral" defined in [Da].
##----------------------------------------------------------
def double_integral(Phi,tau1,tau2,r,s):
   if r == [0,0] or s == [0,0]:
       raise ValueError,'r and s must be valid projective coordinates.'
   if r[0] == 0 and s[1] == 0: # From 0 to infinity
       return double_integral_zero_infty(Phi,tau1,tau2)
   elif s[1] == 0:
       a,b = r
       if b < 0: a,b = -a,-b
       if b == 0: return 1
       if b == 1:
         return double_integral(Phi,tau1-a/b,tau2-a/b,[0,1],[1,0])
       else:
         d = (1/(Zmod(b)(a))).lift()
         if 2*d > b : d -= b
         c = ZZ((a*d-1)/b)

         rr = [c,d] if d >= 0 else [-c,-d]
         i1 = double_integral(Phi,(b*tau1-a)/(d*tau1-c),(b*tau2-a)/(d*tau2-c),[0,1],[1,0])
         i2 = double_integral(Phi,tau1,tau2,rr,[1,0])
         return i1*i2
   else:
      i1= double_integral(Phi,tau1,tau2,r,[1,0])
      i2 = double_integral(Phi,tau1,tau2,s,[1,0])
      return i1/i2


##----------------------------------------------------------------------------
##  indef_integral(tau,r,s)
##
## Input:
##    tau:       Elements of the ``standard affinoid" in H_p consisting
##               of elements in PP_1(C_p) whose natural image in
##               P_1(F_p-bar) does not belong to P_1(F_p).
##    r,s:       Elements of P_1(Q). The cusp r=a/b is
##               represented in the form r=[a,b], with a and b relatively
##               prime integers, and b>=0. By convention infty=[1,0].
##    omega:     The modular form on Gamma_0(p), represented as above.
##
## Output:
##    The indefinite ``multiplicative double integral" defined in [Da].
##----------------------------------------------------------
def indef_integral(Phi,tau,r,s  = None,limits = None):
    p = Phi._map._codomain().parent().base_ring().prime()
    level = ZZ(Phi._map._manin.level()/p)
    I = 1
    if limits is None:
        g,y,mx = xgcd(r[0],r[1])
        gtau = matrix(ZZ,2,2,[r[0],-mx/g,r[1],y/g])
        assert gtau.determinant() == 1
        Vr = find_limits(tau,gtau,level)
        g,y,mx = xgcd(s[0],s[1])
        gtau = matrix(ZZ,2,2,[s[0],-mx/g,s[1],y/g])
        assert gtau.determinant() == 1
        Vs = find_limits(tau,gtau,level)
    else:
        assert s is None
        Vr = limits
        Vs = []
    n_evals = sum((num_evals(t1,t2) for t1,t2 in Vr+Vs))
    verbose('Will perform a total of %s evaluations...'%n_evals)
    for t1,t2 in Vr:
        tmp = double_integral(Phi,t1,t2,[0,1],[1,0])
        I *= tmp
    for t1,t2 in Vs:
        tmp = double_integral(Phi,t1,t2,[0,1],[1,0])
        I /= tmp
    return I



r'''
Integration pairing. The input is a cycle (an element of `H_1(G,\text{Div}^0)`)
and a cocycle (an element of `H^1(G,\text{HC}(\ZZ))`).
Note that it is a multiplicative integral.
'''
def integrate_H1(G,cycle,cocycle,depth = 1,method = 'moments',smoothen_prime = 0,prec = None,parallelize = False,twist=False,progress_bar = False):
    if prec is None:
        prec = cocycle.parent().coefficient_module().base_ring().precision_cap()
    verbose('precision = %s'%prec)
    Cp = cycle.parent().coefficient_module().base_field()
    R = PolynomialRing(Cp,names = 't')
    t = R.gen()
    if method == 'moments':
        integrate_H0 = integrate_H0_moments
    else:
        assert method == 'riemann'
        integrate_H0 = integrate_H0_riemann
    jj = 0
    total_integrals = cycle.size_of_support()
    verbose('Will do %s integrals'%total_integrals)
    input_vec = []
    res = Cp(1)
    for g,divisor in cycle.get_data():
        jj += 1
        if divisor.degree() != 0:
            raise ValueError,'Divisor must be of degree 0'
        gq = g.quaternion_rep
        if twist:
            divisor = divisor.left_act_by_matrix(G.embed(G.wp(),prec).change_ring(Cp))
            gq = G.wp() * gq * G.wp()**-1
        res *= integrate_H0(G,divisor,cocycle,depth,gq,prec,jj,total_integrals,progress_bar,parallelize)
    return res

def evaluate_parallel(hc,gamma,pol,c0):
    HOC = hc.parent()
    mu_e = hc.evaluate(gamma)
    resadd = ZZ(0)
    resmul = ZZ(1)
    K = pol.parent().base_ring()
    p = K.prime()
    if HOC._use_ps_dists:
        newresadd = sum([a*mu_e.moment(i) for a,i in izip(pol.coefficients(),pol.exponents()) if i < len(mu_e._moments)])
    else:
        newresadd = mu_e.evaluate_at_poly(pol)
    resadd += newresadd
    try:
        resmul *= c0**ZZ(mu_e.moment(0).rational_reconstruction())
    except IndexError: pass

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
    hemb = G.embed(h**-1,prec)
    wploc = G.embed(G.wp(),prec)
    if rev == True:
        hemb = hemb * wploc
    a,b,c,d = hemb.list()
    if d == 0:
        return Infinity
    return b/d

r'''
Integration pairing of a function with an harmonic cocycle.
'''
def riemann_sum(G,phi,hc,depth = 1,mult = False):
    prec = max([20,2*depth])
    res = 1 if mult else 0
    K = phi.parent().base_ring()
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

def integrate_H0_riemann(G,divisor,hc,depth,gamma,prec,counter,total_counter,progress_bar,parallelize):
    verbose('Integral %s/%s...'%(counter,total_counter))
    HOC = hc.parent()
    if prec is None:
        prec = HOC.coefficient_module().precision_cap()
    K = divisor.parent().base_ring()
    #R = LaurentSeriesRing(K,'t')
    #R.set_default_prec(prec)
    R = PolynomialRing(K,names = 't').fraction_field()
    t = R.gen()
    phi = prod([(t - P)**ZZ(n) for P,n in divisor],R(1))
    return riemann_sum(G,phi,hc.shapiro_image(G)(gamma),depth,mult = True)

def integrate_H0_moments(G,divisor,hc,depth,gamma,prec,counter,total_counter,progress_bar,parallelize):
    verbose('Integral %s/%s...'%(counter,total_counter))
    p = G.p
    HOC = hc.parent()
    if prec is None:
        prec = HOC.coefficient_module().precision_cap()
    depth = HOC.coefficient_module().precision_cap()
    K = divisor.parent().base_ring()
    QQp = Qp(p,prec)
    R1 = PowerSeriesRing(K,'r1')
    r1 = R1.gen()
    R1.set_default_prec(prec)
    divisor_list = [(P,n) for P,n in divisor]
    resadd = ZZ(0)
    resmul = ZZ(1)
    edgelist = [(1,o,QQ(1)/QQ(p+1)) for o in G.get_covering(1)]
    mem0 = get_memory_usage()
    current_progress = QQ(0)
    while len(edgelist) > 0:
        verbose('Remaining %s edges'%len(edgelist))
        newedgelist = []
        ii = 0
        for parity, edge, wt in edgelist:
            ii += 1
            mem_usage = get_memory_usage() - mem0
            # verbose('mem = %s'%mem_usage)
            if mem_usage > float(8 * 1000):
                verbose('Clearing caches! (mem_usage = %s)'%(mem_usage-mem0))
                G.clear_cache()
                V = HOC.coefficient_module()
                V.clear_cache()
                verbose('Done. New mem_usage = %s'%(get_memory_usage()-mem0))
            rev, h = edge
            a,b,c,d = G.embed(h,prec).list()
            a,b,c,d = K(d),K(-b),K(-c),K(a)
            y0num = R1(1)
            y0den = R1(1)
            for P,n in divisor_list:
                hP = R1([b-d*P,a-P*c])
                if n > 0:
                    y0num *= hP**ZZ(n)
                    y0num = y0num.add_bigoh(prec)
                elif n < 0:
                    y0den *= hP**ZZ(-n)
                    y0den = y0den.add_bigoh(prec)

            assert y0num.valuation() == y0den.valuation()
            y0 = y0num/y0den
            c0 = y0(K(0))
            assert c0 != 0
            c0val = c0.valuation()
            if not all([o.valuation() >= 0 for o in (y0(r1/p)/c0).list() if o != 0]):
            #if not all([o.valuation() >= e + c0val for o,e in zip(y0.coefficients(),y0.exponents())]):
                newedgelist.extend([(parity,o,wt/QQ(p**2)) for o in G.subdivide([edge],parity,2)])
                # newedgelist.extend([(1-parity,o) for o in G.subdivide([edge],parity,1)])
                #assert not rev
                continue
            pol = c0.log(p_branch = 0) + (y0.derivative()/y0).integral()
            if not rev:
                newgamma = G.reduce_in_amalgam(h * gamma)
            else:
                newgamma = G.wp()**-1 * G.reduce_in_amalgam(h * gamma) * G.wp()
            if HOC._use_ps_dists:
                mu_e = hc.evaluate(newgamma,parallelize)
                newresadd = sum(a*mu_e.moment(i) for a,i in izip(pol.coefficients(),pol.exponents()) if i < len(mu_e._moments))
            else:
                mu_e = hc.evaluate(newgamma,parallelize)
                newresadd = mu_e.evaluate_at_poly(pol)
            resadd += newresadd
            try:
                resmul *= c0**ZZ(hc.get_liftee().evaluate(newgamma)[0])
            except IndexError: pass
            if progress_bar:
                current_progress += wt
                #update_progress(float(ii)/float(len(edgelist)),'Integration %s/%s'%(counter,total_counter))
                update_progress(float(current_progress),'Integration %s/%s'%(counter,total_counter))

        edgelist = newedgelist
    val =  resmul.valuation()
    if val != 0:
        verbose('val = %s'%val)
    tmp = p**val * K.teichmuller(p**(-val)*resmul)
    if resadd != 0:
        tmp *= resadd.exp()
    return tmp
