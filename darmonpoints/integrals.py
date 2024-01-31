######################
##                  ##
##  INTEGRATION     ##
##                  ##
######################
from collections import defaultdict
from itertools import chain, groupby, islice, product, starmap, tee
from operator import mul

from sage.all import prod
from sage.arith.misc import algdep
from sage.misc.misc import cputime
from sage.misc.verbose import verbose
from sage.parallel.decorate import fork, parallel
from sage.rings.all import (
    RR,
    ComplexField,
    Infinity,
    LaurentSeriesRing,
    PolynomialRing,
    PowerSeriesRing,
    QuadraticField,
    RealField,
    Zmod,
)
from sage.structure.sage_object import SageObject

from .limits import find_center, num_evals
from .sarithgroup import BTEdge
from .util import *


def act_on_polynomial(P, num, den, N=None):
    if N is None:
        N = P.degree()
    R = num.parent()
    ans = R(0)
    numvec = [R(1)]
    denvec = [R(1)]
    for i in range(N):
        numvec.append(num * numvec[-1])
        denvec.append(den * denvec[-1])
    Plist = P.list()
    for i in range(N + 1):
        ai = Plist[i]
        ans += ai * numvec[i] * denvec[N - i]
    return ans


def double_integral_zero_infty(Phi, tau1, tau2):
    p = Phi.parent().prime()
    K = tau1.parent()
    R = PolynomialRing(K, "x")
    x = R.gen()
    Phi_liftee = Phi._liftee
    try:
        prec = Phi.precision_absolute()
    except AttributeError:
        prec = Phi.precision_relative()
    R1 = PowerSeriesRing(K, "r1", default_prec=prec)
    r1 = R1.gen()
    level = Phi._map._manin.level()
    E0inf = [M2Z([0, -1, level, 0])]
    E0Zp = [M2Z([p, a, 0, 1]) for a in range(p)]

    predicted_evals = num_evals(tau1, tau2)

    a, b, c, d = find_center(p, level, tau1, tau2).list()
    h = M2Z([a, b, c, d])
    E = [h * e0 for e0 in E0Zp + E0inf]

    resadd = 0
    resmul = 1
    total_evals = 0
    percentage = QQ(0)
    ii = 0
    f = (x - tau2) / (x - tau1)
    while len(E) > 0:
        ii += 1
        increment = QQ((100 - percentage) / len(E))
        verbose(
            "remaining %s percent (and done %s of %s evaluations)"
            % (RealField(10)(100 - percentage), total_evals, predicted_evals)
        )
        newE = []
        for e in E:
            a, b, c, d = e.list()
            assert ZZ(c) % level == 0
            try:
                y0 = f((a * r1 + b) / (c * r1 + d))
                val = y0(y0.parent().base_ring()(0))
                if all([xx.valuation(p) > 0 for xx in (y0 / val - 1).list()]):
                    if total_evals % 100 == 0:
                        Phi._map._codomain.clear_cache()
                    pol = val.log(p_branch=0) + ((y0.derivative() / y0).integral())
                    V = [0] * pol.valuation() + pol.shift(-pol.valuation()).list()

                    try:
                        phimap = Phi._map(M2Z([b, d, a, c]))
                    except OverflowError:
                        print(a, b, c, d)
                        raise OverflowError("Matrix too large?")
                    # mu_e0 = ZZ(phimap.moment(0).rational_reconstruction())
                    mu_e0 = ZZ(Phi_liftee._map(M2Z([b, d, a, c])).moment(0))
                    mu_e = [mu_e0] + [phimap.moment(o).lift() for o in range(1, len(V))]
                    resadd += sum(starmap(mul, zip(V, mu_e)))
                    resmul *= val**mu_e0
                    percentage += increment
                    total_evals += 1
                else:
                    newE.extend([e * e0 for e0 in E0Zp])
            except ZeroDivisionError:
                # raise RuntimeError('Probably not enough working precision...')
                newE.extend([e * e0 for e0 in E0Zp])
        E = newE
    verbose("total evaluations = %s" % total_evals)
    val = resmul.valuation()
    return p**val * K.teichmuller(p ** (-val) * resmul) * resadd.exp()


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
def double_integral(Phi, tau1, tau2, r, s):
    if r == [0, 0] or s == [0, 0]:
        raise ValueError("r and s must be valid projective coordinates.")
    if r[0] == 0 and s[1] == 0:  # From 0 to infinity
        return double_integral_zero_infty(Phi, tau1, tau2)
    elif s[1] == 0:
        a, b = r
        if b < 0:
            a, b = -a, -b
        if b == 0:
            return 1
        if b == 1:
            return double_integral(Phi, tau1 - a / b, tau2 - a / b, [0, 1], [1, 0])
        else:
            d = (1 / (Zmod(b)(a))).lift()
            if 2 * d > b:
                d -= b
            c = ZZ((a * d - 1) / b)

            rr = [c, d] if d >= 0 else [-c, -d]
            i1 = double_integral(
                Phi,
                (b * tau1 - a) / (d * tau1 - c),
                (b * tau2 - a) / (d * tau2 - c),
                [0, 1],
                [1, 0],
            )
            i2 = double_integral(Phi, tau1, tau2, rr, [1, 0])
            return i1 * i2
    else:
        i1 = double_integral(Phi, tau1, tau2, r, [1, 0])
        i2 = double_integral(Phi, tau1, tau2, s, [1, 0])
        return i1 / i2


def log_pseries(R, x, prec=None):
    r"""
    Calculate efficiently log(1 - x*z), where z is the variable of R
    Doing it with power series built-in log is about 10 times slower...
    """
    if x.valuation() <= 0:
        raise ValueError("Valuation problem")
    K = R.base_ring()
    if prec is None:
        prec = R.default_precision()
    v = [K.zero(), K(x)]
    xpow = K(x)
    for m in range(2, prec + 1):
        xpow *= x
        v.append(xpow / QQ(m))
    return -R(v)


def lift_to_locally_analytic(G, divisor, prec=None, depth=1):
    if depth % 2 != 1:
        raise NotImplementedError("Need to allow for reversed edges.")
    K = divisor.parent().base_ring()
    if prec is None:
        prec = K.precision_cap()
    p = G.p
    R = PolynomialRing(K, "r")
    wplocinv = G.wp
    edgelist = [
        ((-1) ** (depth + 1), o, QQ(1) / QQ(p + 1)) for o in G.get_covering(depth)
    ]
    while len(edgelist) > 0:
        newedgelist = []
        ii = 0
        for parity, (rev, h), wt in edgelist:
            ii += 1
            assert not rev  # TODO: allow for reversed edges as well
            a, b, c, d = (K(o) for o in G.embed(h, prec).list())
            try:
                c0unit = K.one()
                c0val = 0
                pol = R.zero()
                for P, n in divisor:
                    hp0 = K(a * P + b)
                    pol += QQ(n) * log_pseries(R, K(c * P + d) / hp0, prec)
                    c0unit *= (-hp0).unit_part() ** n
                    c0val += n * hp0.valuation()
                pol += c0unit.log(0)
                yield ((h, rev), pol, c0val, c0unit)
            except ValueError as msg:
                verbose("Subdividing because (%s)..." % str(msg))
                newedgelist.extend(
                    [
                        ((-1) ** 2 * parity, o, wt / QQ(p**2))
                        for o in G.subdivide([(rev, h)], parity, 2)
                    ]
                )
                continue
        edgelist = newedgelist


r"""
Integration pairing. The input is a cycle (an element of `H_1(G,\text{Div}^0)`)
and a cocycle (an element of `H^1(G,\text{HC}(\ZZ))`).
Note that it is a multiplicative integral.
"""


def integrate_H1(
    G,
    cycle,
    cocycle,
    depth=1,
    prec=None,
    twist=False,
    progress_bar=False,
    multiplicative=True,
    return_valuation=True,
):
    if not cycle.is_degree_zero_valued():
        raise ValueError("Cycle should take values in divisors of degree 0")
    if prec is None:
        prec = cocycle.parent().coefficient_module().base_ring().precision_cap()
    verbose("precision = %s" % prec)
    Cp = cycle.parent().coefficient_module().base()
    R = PolynomialRing(Cp, names="t")
    t = R.gen()
    total_integrals = cycle.size_of_support()
    verbose("Will do %s integrals" % total_integrals)
    resmul = Cp(1)
    resadd = Cp(0)
    resval = ZZ(0)
    for g, D in cycle:
        if twist:
            D = D.left_act_by_matrix(G.embed(G.wp(), prec).change_ring(Cp))
            g = g.conjugate_by(G.wp() ** -1)
        for (h, rev), pol, c0val, c0unit in lift_to_locally_analytic(G, D, prec, depth):
            mu = cocycle.evaluate(g, h, at_identity=G.use_shapiro())
            mu0 = cocycle["liftee"].evaluate(g, h, at_identity=G.use_shapiro())[0]
            newresadd = sum(
                a * mu.moment(i)
                for a, i in zip(pol.coefficients(), pol.exponents())
                if i < len(mu.moments())
            )
            newresval = c0val * ZZ(mu0)
            newresmul = c0unit ** ZZ(mu0)
            if rev:
                newresadd = -newresadd
                newresval = -newresval
                newresmul = newresmul**-1
            resadd += newresadd
            resval += newresval
            resmul *= newresmul
    if not multiplicative:
        return resadd, resval, resmul if return_valuation else resadd
    else:
        return Cp.prime() ** resval * Cp.teichmuller(resmul) * resadd.exp()  # DEBUG


def integrate_H1_riemann(
    G, cycle, cocycle, depth, prec=None, twist=False, progress_bar=False
):
    if not cycle.is_degree_zero_valued():
        raise ValueError("Cycle should take values in divisors of degree 0")
    if prec is None:
        prec = cocycle.parent().coefficient_module().base_ring().precision_cap()
    verbose("precision = %s" % prec)
    Cp = cycle.parent().coefficient_module().base()
    R = PolynomialRing(Cp, names="t")
    t = R.gen()
    total_integrals = cycle.size_of_support()
    verbose("Will do %s integrals" % total_integrals)
    R = PolynomialRing(Cp, names="t").fraction_field()
    t = R.gen()
    resmul = Cp(1)
    resadd = Cp(0)
    resval = ZZ(0)
    try:
        cocycle = cocycle["liftee"]
    except KeyError:
        pass
    for g, D in cycle:
        if twist:
            D = D.left_act_by_matrix(G.embed(G.wp(), prec).change_ring(Cp))
            g = g.conjugate_by(G.wp() ** -1)
        phiD = lambda t: prod([(t - P) ** ZZ(n) for P, n in D], Cp(1))
        resmul *= Cp(
            riemann_sum(
                G,
                phiD,
                ShapiroImage(G, cocycle)(g.quaternion_rep),
                depth,
                mult=True,
                progress_bar=progress_bar,
                K=Cp,
            )
        )
    return resmul


def sample_point(G, e, prec=20):
    r"""
    Returns a point in U_h = (e)^{-1} Z_p.
    """
    rev, h = e
    hemb = G.embed(set_immutable(h**-1), prec)
    wploc = G.embed(G.wp(), prec)
    if rev == True:
        hemb = hemb * wploc
    a, b, c, d = hemb.list()
    if d == 0:
        return Infinity
    return b / d


def get_basic_integral(G, cocycle, gamma, center, j, prec=None):
    p = G.p
    HOC = cocycle.parent()
    V = HOC.coefficient_module()

    if prec is None:
        prec = V.precision_cap()
    Cp = Qp(p, prec)
    verbose("precision = %s" % prec)
    R = PolynomialRing(Cp, names="t")
    PS = PowerSeriesRing(Cp, names="z")
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
        mu_e = cycle.evaluate(gamma, h, twist=rev, at_identity=G.use_shapiro())
        a, b, c, d = (Cp(o) for o in G.embed(h, prec).list())
        pol = (
            (PS(d * z + b) / PS(c * z + a) - Cp.teichmuller(center)) ** j
        ).polynomial()
        resadd += sum(
            a * mu_e.moment(i)
            for a, i in zip(pol.coefficients(), pol.exponents())
            if i < len(mu_e.moments())
        )
    return resadd


class ShapiroImage(SageObject):
    def __init__(self, G, cocycle):
        self.G = G
        self.cocycle = cocycle

    def __call__(self, gamma):
        return CoinducedElement(self.G, self.cocycle, gamma)


class CoinducedElement(SageObject):
    def __init__(self, G, cocycle, gamma):
        self.G = G
        self.cocycle = cocycle
        self.gamma = gamma

    def __call__(self, h, check=False):
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


r"""
Integration pairing of a function with an harmonic cocycle.
"""


def riemann_sum(G, phi, hc, depth=1, mult=False, progress_bar=False, K=None):
    prec = max([20, 2 * depth])
    res = 1 if mult else 0
    if K is None:
        K = phi.parent().base_ring()
    cover = G.get_covering(depth)
    n_ints = 0
    for e in cover:
        if n_ints % 500 == 499:
            verbose("Done %s percent" % (100 * RealField(10)(n_ints) / len(cover)))
        if progress_bar:
            update_progress(
                float(RealField(10)(n_ints + 1) / len(cover)), "Riemann sum"
            )
        n_ints += 1
        val = hc(e)
        vmom = val[0]  # .moment(0)
        if vmom.parent().is_exact():
            hce = ZZ(vmom)
        else:
            hce = ZZ(vmom.rational_reconstruction())
        if hce == 0:
            continue
        # verbose('hc = %s'%hce)
        te = sample_point(G, e, prec)
        if te == Infinity:
            continue
        if mult:
            res *= phi(K(te)) ** hce
        else:
            res += phi(K(te)) * hce
    return res
