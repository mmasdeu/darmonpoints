######################
##                  ##
##  INTEGRATION     ##
##                  ##
######################
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,LaurentSeriesRing,PowerSeriesRing, Infinity,Zmod
from sage.all import prod
from sage.parallel.decorate import fork,parallel
from sage.misc.getusage import get_memory_usage
from sage.structure.sage_object import SageObject

from collections import defaultdict
from itertools import product,chain,groupby,islice,tee,starmap
from operator import mul

from .util import *
from .sarithgroup import BTEdge
from .limits import num_evals,find_center

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
    Phi_liftee = Phi._liftee
    try:
        R1.set_default_prec(Phi.precision_absolute())
    except AttributeError:
        R1.set_default_prec(Phi.precision_relative())
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
                        print(a,b,c,d)
                        raise OverflowError('Matrix too large?')
                    # mu_e0 = ZZ(phimap.moment(0).rational_reconstruction())
                    mu_e0 = ZZ(Phi_liftee._map(M2Z([b,d,a,c])).moment(0))
                    mu_e = [mu_e0] + [phimap.moment(o).lift() for o in range(1,len(V))]
                    resadd += sum(starmap(mul,zip(V,mu_e)))
                    resmul *= val**mu_e0
                    percentage += increment
                    total_evals += 1
                else:
                    newE.extend([e*e0 for e0 in E0Zp])
            except ZeroDivisionError:
                #raise RuntimeError('Probably not enough working precision...')
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
       raise ValueError('r and s must be valid projective coordinates.')
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
      i1 = double_integral(Phi,tau1,tau2,r,[1,0])
      i2 = double_integral(Phi,tau1,tau2,s,[1,0])
      return i1/i2

r'''
Integration pairing. The input is a cycle (an element of `H_1(G,\text{Div}^0)`)
and a cocycle (an element of `H^1(G,\text{HC}(\ZZ))`).
Note that it is a multiplicative integral.
'''
def integrate_H1(G,cycle,cocycle,depth = 1,prec = None,parallelize = False,twist=False,progress_bar = False,multiplicative = True, return_valuation = False):
    if prec is None:
        prec = cocycle.parent().coefficient_module().base_ring().precision_cap()
    verbose('precision = %s'%prec)
    Cp = cycle.parent().coefficient_module().base_field()
    R = PolynomialRing(Cp,names = 't')
    t = R.gen()
    jj = 0
    total_integrals = cycle.size_of_support()
    verbose('Will do %s integrals'%total_integrals)
    input_vec = []
    resmul = Cp(1)
    resadd = Cp(0)
    resval = ZZ(0)
    for g,divisor in cycle.get_data():
        jj += 1
        if divisor.degree() != 0:
            raise ValueError('Divisor must be of degree 0. Now it is of degree %s. And g = %s.'%(divisor.degree(),g.quaternion_rep))
        if twist:
            divisor = divisor.left_act_by_matrix(G.embed(G.wp(),prec).change_ring(Cp))
            g = g.conjugate_by(G.wp()**-1)
        newresadd, newresmul, newresval = integrate_H0(G,divisor,cocycle,depth,g,prec,jj,total_integrals,progress_bar,parallelize)
        resadd += newresadd
        resmul *= newresmul
        resval += newresval
    if not multiplicative:
        if return_valuation:
            return resadd, resval, Cp.teichmuller(resmul)
        else:
            return resadd
    else:
        return Cp.prime()**resval * Cp.teichmuller(resmul) * resadd.exp()

def evaluate_parallel(hc,gamma,pol,c0):
    HOC = hc.parent()
    mu_e = hc.evaluate(gamma)
    resadd = ZZ(0)
    resmul = ZZ(1)
    K = pol.parent().base_ring()
    p = K.prime()
    if HOC._use_ps_dists:
        newresadd = sum([a*mu_e.moment(i) for a,i in zip(pol.coefficients(),pol.exponents()) if i < len(mu_e._moments)])
    else:
        newresadd = mu_e.evaluate_at_poly(pol,K,HOC.precision_cap())
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
    hemb = G.embed(set_immutable(h**-1),prec)
    wploc = G.embed(G.wp(),prec)
    if rev == True:
        hemb = hemb * wploc
    a,b,c,d = hemb.list()
    if d == 0:
        return Infinity
    return b/d

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
            assert self.G.reduce_in_amalgam(b) == 1
        a = self.G.reduce_in_amalgam(b * self.gamma)
        if self.G.use_shapiro():
            ans = self.cocycle.evaluate_and_identity(a)
        else:
            ans = self.cocycle.evaluate(a)
        if rev == False:
            return ans
        else:
            return -ans

def integrate_H0(G,divisor,hc,depth,gamma,prec,counter,total_counter,progress_bar,parallelize):
    # verbose('Integral %s/%s...'%(counter,total_counter))
    p = G.p
    HOC = hc.parent()
    if prec is None:
        prec = HOC.coefficient_module().precision_cap()
    try:
        coeff_depth = HOC.coefficient_module().precision_cap()
    except AttributeError:
        coeff_depth = HOC.coefficient_module().coefficient_module().precision_cap()
    K = divisor.parent().base_ring()
    QQp = Qp(p,prec)
    R = PolynomialRing(K,'r')
    divisor_list = [(P,n) for P,n in divisor]
    resadd = ZZ(0)
    resval = ZZ(0)
    resmul = ZZ(1)
    edgelist = [(1,o,QQ(1)/QQ(p+1)) for o in G.get_covering(depth)]
    while len(edgelist) > 0:
        newedgelist = []
        ii = 0
        for parity, (rev, h), wt in edgelist:
            ii += 1
            a,b,c,d = [K(o) for o in G.embed(h,prec).list()]
            try:
                c0unit = K.one()
                c0val = 0
                pol = R.zero()
                for P,n in divisor_list:
                    if P == Infinity:
                        continue
                    else:
                        hp0 = K(b + a * P)
                        hp1 = K(d + c * P)
                        if hp1.valuation() <= hp0.valuation():
                            raise ValueError('Valuation problem')
                    x = hp1 / hp0
                    v = [K.zero(),K(x)]
                    xpow = K(x)
                    for m in range(2, coeff_depth + 1):
                        xpow *= x
                        v.append( xpow / QQ(m) )
                    pol -= QQ(n) * R(v)
                    c0unit *= (-hp0).unit_part() ** n
                    c0val += n * hp0.valuation()
                pol += c0unit.log( p_branch = 0 )
                newgamma = G.reduce_in_amalgam(h * gamma.quaternion_rep, return_word = False)
                if rev:
                    newgamma = newgamma.conjugate_by(G.wp())
                if G.use_shapiro():
                    mu_e = hc.evaluate_and_identity(newgamma)
                else:
                    mu_e = hc.evaluate(newgamma)
            except ValueError as msg:
                verbose('Subdividing because (%s)...'%str(msg))
                newedgelist.extend([(parity,o,wt/QQ(p**2)) for o in G.subdivide([(rev, h)],parity,2)])
                continue
            if HOC._use_ps_dists:
                resadd += sum(a * mu_e.moment(i) for a,i in zip(pol.coefficients(),pol.exponents()) if i < len(mu_e._moments))
            else:
                resadd += mu_e.evaluate_at_poly(pol, K, coeff_depth)
            try:
                if G.use_shapiro():
                    tmp = hc['liftee'].evaluate_and_identity(newgamma)
                else:
                    tmp = hc['liftee'].evaluate(newgamma)
                resval += c0val * ZZ(tmp[0])
                resmul *= c0unit**ZZ(tmp[0])
            except IndexError: pass
            if progress_bar:
                update_progress(float(QQ(ii)/QQ(len(edgelist))),'Integration %s/%s'%(counter,total_counter))

        edgelist = newedgelist
    return resadd, resmul, resval

def get_basic_integral(G,cocycle,gamma, center, j, prec=None):
    p = G.p
    HOC = cocycle.parent()
    V = HOC.coefficient_module()

    if prec is None:
        prec = V.precision_cap()
    Cp = Qp(p, prec)
    verbose('precision = %s'%prec)
    R = PolynomialRing(Cp,names = 't')
    PS = PowerSeriesRing(Cp, names = 'z')
    t = R.gen()
    z = PS.gen()

    if prec is None:
        prec = V.precision_cap()
    try:
        coeff_depth = V.precision_cap()
    except AttributeError:
        coeff_depth = V.coefficient_module().precision_cap()
    resadd = ZZ(0)
    edgelist = G.get_covering(1)[1:]
    for rev, h in edgelist:
        a,b,c,d = [Cp(o) for o in G.embed(h,prec).list()]
        try:
            c0val = 0
            pol =  PS(d * z + b) / PS(c * z + a)
            pol -= Cp.teichmuller(center)
            pol = pol**j
            pol = pol.polynomial()
            newgamma = G.Gpn(G.reduce_in_amalgam(h * gamma.quaternion_rep, return_word = False))
            if rev: # DEBUG
                newgamma = newgamma.conjugate_by(G.wp())
            if G.use_shapiro():
                mu_e = cocycle.evaluate_and_identity(newgamma)
            else:
                mu_e = cocycle.evaluate(newgamma)
        except AttributeError:
            verbose('...')
            continue
        if HOC._use_ps_dists:
            tmp = sum(a * mu_e.moment(i) for a,i in zip(pol.coefficients(),pol.exponents()) if i < len(mu_e._moments))
        else:
            tmp = mu_e.evaluate_at_poly(pol, Cp, coeff_depth)
        resadd += tmp
        try:
            if G.use_shapiro():
                tmp = cocycle['liftee'].evaluate_and_identity(newgamma)
            else:
                tmp = cocycle['liftee'].evaluate(newgamma)
        except IndexError: pass
    return resadd
