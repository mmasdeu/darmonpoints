######################
##                  ##
##  INTEGRATION     ##
##                  ##
######################
from collections import defaultdict
from itertools import chain, groupby, islice, product, starmap, tee
from operator import mul

from sage.arith.misc import algdep
from sage.misc.misc import cputime
from sage.misc.misc_c import prod
from sage.misc.verbose import verbose
from sage.parallel.decorate import fork, parallel
from sage.rings.complex_mpfr import ComplexField
from sage.rings.finite_rings.integer_mod_ring import IntegerModRing as Zmod
from sage.rings.infinity import Infinity
from sage.rings.laurent_series_ring import LaurentSeriesRing
from sage.rings.number_field.number_field import QuadraticField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.real_mpfr import RR, RealField
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


def _locally_analytic_data(G, divisor, prec=None, depth=1):
    r"""
    The data of :func:`lift_to_locally_analytic`, without building the power
    series: for each edge, yields ``((h, rev), xs, c0val, c0unit)``, where
    ``xs`` is the list of pairs ``(x_P, n_P)`` such that the series is
    `\log(c_0) + \sum_P n_P \log(1 - x_P z)`.
    """
    if depth % 2 != 1:
        raise NotImplementedError("Need to allow for reversed edges.")
    K = divisor.parent().base_ring()
    if prec is None:
        prec = K.precision_cap()
    p = G.p
    edgelist = [
        ((-1) ** (depth + 1), o, QQ(1) / QQ(p + 1)) for o in G.get_covering(depth)
    ]
    while len(edgelist) > 0:
        newedgelist = []
        for parity, (rev, h), wt in edgelist:
            assert not rev  # TODO: allow for reversed edges as well
            a, b, c, d = (K(o) for o in G.embed(h, prec).list())
            c0unit = K.one()
            c0val = 0
            xs = []
            subdivide = False
            for P, n in divisor:
                hp0 = K(a * P + b)
                x = K(c * P + d) / hp0
                if x.valuation() <= 0:
                    subdivide = True
                    break
                xs.append((x, QQ(n)))
                c0unit *= (-hp0).unit_part() ** n
                c0val += n * hp0.valuation()
            if subdivide:
                verbose("Subdividing because (Valuation problem)...")
                newedgelist.extend(
                    [
                        ((-1) ** 2 * parity, o, wt / QQ(p**2))
                        for o in G.subdivide([(rev, h)], parity, 2)
                    ]
                )
                continue
            yield ((h, rev), xs, c0val, c0unit)
        edgelist = newedgelist


def _pair_with_moments(K, xs, logc0, moments, prec, inverses):
    r"""
    The pairing of `\log(c_0) + \sum_P n_P \log(1 - x_P z)` (truncated at
    degree ``prec``) with the moments ``moments`` (elements of ``K``), that
    is `\log(c_0) \mu_0 - \sum_{m \geq 1} (\sum_P n_P x_P^m) \mu_m / m`.
    """
    M = min(prec, len(moments) - 1)
    S = [K.zero()] * (M + 1)
    for x, n in xs:
        xpow = K.one()
        for m in range(1, M + 1):
            xpow = xpow * x
            S[m] += n * xpow
    ans = logc0 * moments[0] if not logc0.is_zero() else K.zero()
    for m in range(1, M + 1):
        ans -= S[m] * inverses[m] * moments[m]
    return ans


# Use _collect_pairing_points from this number of moments on (below, it is
# slower than pairing with the moments; above, it is faster, and it does not
# need to keep the matrices of moments, which take a lot of memory)
_FAST_PAIRING_MIN_PREC = 150


def _fast_pairing_data(G, cocycle, Cp, prec):
    r"""
    The data used by :func:`_pair_cocycle_with_series`, or ``None`` if it
    does not apply (``cocycle`` must take values in ``OCVn``, without
    Shapiro's lemma, and ``Cp`` must be `\QQ_p` or a quadratic unramified
    extension).
    """
    from .ocmodule import OCVn
    from .theta_additive import _ok_coordinates

    try:
        H = cocycle.parent()
        V = H.coefficient_module()
        if not (
            isinstance(V, OCVn)
            and not G.use_shapiro()
            and not H._trivial_action
            and H._acting_matrix is not None
        ):
            return None
        O = _ok_coordinates(Cp)
    except (AttributeError, NotImplementedError):
        return None
    if O.e != 1 or O.d > 2 or O._kind not in ("Qp", "unramified"):
        return None
    p = ZZ(Cp.prime())
    n = V._depth - 1
    if n < _FAST_PAIRING_MIN_PREC:
        # At low precision, the matrices of moments are small and caching
        # them is faster
        return None
    N = p**n
    if O.d == 2:
        # g^2 = t1 g + t0
        f = [ZZ(c.lift()) for c in Cp.defining_polynomial().list()]
        if f[2] != 1:
            return None
        t0, t1 = -f[0], -f[1]
    else:
        t0, t1 = 0, 0
    # f_i(Y) = sum_{m >= 1} v_i[m] p^m / m Y^m, where v_i are the moments of
    # the value at the i-th generator: then sum_m v_i[m] y^m / m = f_i(y / p)
    M = min(n, prec)
    polys = []
    for v in cocycle.values():
        mom = v._val.list()
        cf = [ZZ(0)]
        for m in range(1, min(M, len(mom) - 1) + 1):
            e = m.valuation(p) if hasattr(m, "valuation") else ZZ(m).valuation(p)
            unit = ZZ(m) // p**e
            cf.append(ZZ(mom[m].lift()) * p ** (m - e) * unit.inverse_mod(N) % N)
        polys.append((cf, Cp(ZZ(mom[0].lift()))))
    acc = [
        dict(logc0=Cp(0), unit=[ZZ(1)] + [ZZ(0)] * (O.d - 1), points=[], weights=[])
        for _ in polys
    ]
    return dict(H=H, O=O, p=p, N=N, d=O.d, t0=t0, t1=t1, polys=polys, local={}, acc=acc)


def _collect_pairing_points(G, cocycle, g, h, xs, logc0, data):
    r"""
    Record the contribution to the integral of the pairing of the series
    `\log(c_0) + \sum_P n_P \log(1 - x_P z)` with the moments of
    ``cocycle.evaluate(g, h)``, without computing these moments (it is
    finished by :func:`_finish_pairing`).

    The value is `hp \cdot \sum_i \partial_i(w) c(\gamma_i)` (see
    ``ArithCohElement.evaluate``), a sum of terms `M(x) c(\gamma_i)` for
    `2 \times 2` matrices `x`. Pairing a series with the moments of `M(x)\mu`
    is pairing the series composed with the Moebius map of `x` with those of
    `\mu` (modulo the filtration of overconvergent distributions, which is
    the precision of the moments anyway), and since `\sum_P n_P = 0` the
    composed series has the same form:

    .. MATH::

        \log(c_0) + \sum_P n_P \log(1 - x_P b/d) + \sum_P n_P \log(1 - y_P z),
        \qquad y_P = \frac{a x_P - c}{d - b x_P},

    for `x = [[a, b], [c, d]]`. So, for each generator `\gamma_i`, only the
    constant term and the points `y_P / p` (with their weights) are recorded.
    """
    H = data["H"]
    O, p, N = data["O"], data["p"], data["N"]
    S = H.S_arithgroup()
    Gpn = H.group()
    K = logc0.parent()
    try:
        gq = g.quaternion_rep
    except AttributeError:
        gq = g
    hp = S.reduce_in_amalgam(h, return_word=False)
    he = hp**-1 * h
    newg = S.reduce_in_amalgam(he * gq, return_word=False)
    x = newg if newg.parent() is Gpn else Gpn(newg)
    fgrad = H.fox_gradient(tuple(x.word_rep))
    from .moments import mobius_transform_points

    Mh = Gpn(hp).matrix()
    local = data["local"]
    d, t0, t1 = data["d"], data["t0"], data["t1"]
    xcoords = [[o % N for o in O.coords(xP)] for xP, _ in xs]
    ns = [ZZ(nP) for _, nP in xs]
    for i, A in enumerate(fgrad):
        mono = A.monomial_coefficients(copy=False)
        if not mono:
            continue
        acc = data["acc"][i]
        asum = 0
        for gp, coeff in mono.items():
            if coeff == 0:
                continue
            try:
                Mg = local[gp]
            except KeyError:
                Mg = local[gp] = gp.matrix()
            a, b, c, dd = (ZZ(o.lift()) % N for o in (Mh * Mg).list())
            asum += coeff
            pts, ws, u = mobius_transform_points(
                a, b, c, dd, xcoords, ns, ZZ(coeff), p, N, t0, t1, d
            )
            acc["points"].extend(pts)
            acc["weights"].extend(ws)
            acc["unit"] = _ok_mul(acc["unit"], u, N, d, t0, t1)
        acc["logc0"] += asum * logc0


def _ok_mul(x, y, N, d, t0, t1):
    r"""
    Product of the coordinates ``x`` and ``y`` in `\ZZ[g]/(g^2 - t_1 g - t_0)`
    (``d = 2``) or `\ZZ` (``d = 1``), modulo ``N``.
    """
    if d == 1:
        return [x[0] * y[0] % N]
    w = x[1] * y[1]
    return [(x[0] * y[0] + t0 * w) % N, (x[0] * y[1] + x[1] * y[0] + t1 * w) % N]


def _power_sums(points, weights, n, N, d, t0, t1):
    r"""
    The coordinates (``d`` lists of length ``n``) of the power sums
    `\sum_k w_k y_k^m` for `0 \leq m < n`, modulo ``N``, for points `y_k` of
    `\ZZ[g]/(g^2 - t_1 g - t_0)` (``d = 2``) or `\ZZ` (``d = 1``).

    They are the coefficients of `\sum_k w_k / (1 - y_k T)`, which is computed
    by adding the fractions in pairs (a product tree), truncating at `T^n`,
    and expanding the final fraction.

    EXAMPLES::

        sage: from darmonpoints.integrals import _power_sums
        sage: _power_sums([[2], [3]], [1, 5], 4, 1000, 1, 0, 0)
        [[6, 17, 49, 143]]
        sage: [2^m + 5 * 3^m for m in range(4)]
        [6, 17, 49, 143]
    """
    R = PolynomialRing(ZZ, "T")
    T = R.gen()

    def red(P):
        return [f.truncate(n) % N for f in P]

    def mul(A, B):
        if d == 1:
            return red([A[0]._mul_trunc_(B[0], n)])
        p00 = A[0]._mul_trunc_(B[0], n)
        p11 = A[1]._mul_trunc_(B[1], n)
        p01 = A[0]._mul_trunc_(B[1], n) + A[1]._mul_trunc_(B[0], n)
        return red([p00 + t0 * p11, p01 + t1 * p11])

    def add(A, B):
        return red([a + b for a, b in zip(A, B)])

    from .moments import chunk_fractions

    one = [R.one()] + [R.zero()] * (d - 1)
    if not points:
        return [[ZZ(0)] * n for _ in range(d)]
    # Leaves: the fractions of chunks of points, computed in C
    nodes = [
        ([R(c) for c in num], [R(c) for c in den])
        for num, den in chunk_fractions(points, weights, 32, n, N, t0, t1, d)
    ]
    while len(nodes) > 1:
        new = []
        for k in range(0, len(nodes) - 1, 2):
            (N1, D1), (N2, D2) = nodes[k], nodes[k + 1]
            new.append((add(mul(N1, D2), mul(N2, D1)), mul(D1, D2)))
        if len(nodes) % 2:
            new.append(nodes[-1])
        nodes = new
    num, den = nodes[0]
    # Inverse of den (whose constant term is 1) by Newton's method
    inv = one
    prec = 1
    while prec < n:
        prec = min(2 * prec, n)
        e = mul(den, inv)
        e = [-f for f in e]
        e[0] += 2
        inv = mul(inv, e)
    S = mul(num, inv)
    return [f.padded_list(n) for f in S]


def _finish_pairing(data):
    r"""
    The sum of the pairings recorded by :func:`_collect_pairing_points`.
    """
    O, p, N, d = data["O"], data["p"], data["N"], data["d"]
    total = None
    for (cf, v0), acc in zip(data["polys"], data["acc"]):
        K = v0.parent()
        n = len(cf)
        S = _power_sums(acc["points"], acc["weights"], n, N, d, data["t0"], data["t1"])
        coords = [sum(c * s for c, s in zip(cf[1:], Sr[1:])) % N for Sr in S]
        unit = O.element(acc["unit"], K.precision_cap())
        val = (acc["logc0"] + unit.log(0)) * v0 - O.element(coords, K.precision_cap())
        total = val if total is None else total + val
    return total


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
    twist=None,
    progress_bar=False,
    multiplicative=True,
    return_valuation=True,
):
    if not cycle.is_degree_zero_valued():
        raise ValueError("Cycle should take values in divisors of degree 0")
    if prec is None:
        prec = cocycle.parent().coefficient_module().base_ring().precision_cap()
    if twist is None:
        twist = getattr(cycle, "twist", False)

    verbose("precision = %s" % prec)
    Cp = cycle.parent().coefficient_module().base()
    R = PolynomialRing(Cp, names="t")
    t = R.gen()
    total_integrals = cycle.size_of_support()
    verbose("Will do %s integrals" % total_integrals)
    resmul = Cp(1)
    resadd = Cp(0)
    resval = ZZ(0)
    inverses = [None] + [Cp(QQ(1) / m) for m in range(1, prec + 1)]
    fast = _fast_pairing_data(G, cocycle, Cp, prec)
    for g, D in cycle:
        if twist:
            D = D.left_act_by_matrix(G.embed(G.wp(), prec).change_ring(Cp))
            g = g.conjugate_by(G.wp() ** -1)
        for (h, rev), xs, c0val, c0unit in _locally_analytic_data(G, D, prec, depth):
            mu0 = cocycle["liftee"].evaluate(g, h, at_identity=G.use_shapiro())[0]
            if fast is not None:
                if rev:
                    raise NotImplementedError("reversed edges")
                _collect_pairing_points(G, cocycle, g, h, xs, c0unit.log(0), fast)
                newresadd = 0
            else:
                mu = cocycle.evaluate(g, h, at_identity=G.use_shapiro())
                nmom = len(mu.moments())
                moments = [Cp(mu.moment(i)) for i in range(min(nmom, prec + 1))]
                newresadd = _pair_with_moments(
                    Cp, xs, c0unit.log(0), moments, prec, inverses
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
    if fast is not None:
        resadd += _finish_pairing(fast)
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
    if rev is True:
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
        mu_e = cocycle.evaluate(gamma, h, twist=rev, at_identity=G.use_shapiro())
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
        if rev is False:
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
        t_e = sample_point(G, e, prec)
        if t_e == Infinity:
            continue
        if mult:
            res *= phi(K(t_e)) ** hce
        else:
            res += phi(K(t_e)) * hce
    return res
