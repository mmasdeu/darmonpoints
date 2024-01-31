import configparser
import sys
import types
from functools import reduce
from itertools import chain, groupby, islice, product, starmap, tee

from sage.algebras.quatalg.quaternion_algebra import QuaternionAlgebra
from sage.arith.all import divisors, kronecker_symbol, next_prime
from sage.arith.functions import lcm
from sage.arith.misc import valuation
from sage.calculus.var import var
from sage.functions.generalized import sgn
from sage.functions.transcendental import Function_zeta
from sage.groups.finitely_presented import wrap_FpGroup
from sage.interfaces.gp import gp
from sage.libs.pari.all import PariError, pari
from sage.matrix.all import Matrix, matrix
from sage.misc.all import cached_method, cartesian_product_iterator
from sage.misc.cachefunc import cached_function
from sage.misc.functional import cyclotomic_polynomial
from sage.misc.latex import LatexExpr, latex
from sage.misc.misc_c import prod
from sage.misc.sage_eval import sage_eval
from sage.misc.verbose import get_verbose, set_verbose, verbose
from sage.modular.modform.constructor import CuspForms, EisensteinForms
from sage.modules.fg_pid.fgp_module import FGP_Module, FGP_Module_class
from sage.rings.all import CC, QQ, RR, ZZ, Qp, RealField
from sage.rings.big_oh import O
from sage.rings.fast_arith import prime_range
from sage.rings.finite_rings.integer_mod_ring import IntegerModRing, Zmod
from sage.rings.infinity import Infinity
from sage.rings.padics.padic_generic import local_print_mode
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.schemes.elliptic_curves.constructor import (
    EllipticCurve,
    EllipticCurve_from_c4c6,
)
from sage.sets.primes import Primes
from sage.structure.factorization import Factorization


def is_smooth(x, B):
    for p in B:
        x /= p ** (valuation(x, p))
    return x == 1 or x == -1


def is_infinity(x):
    try:
        return x.is_infinity()
    except AttributeError:
        pass
    if x is Infinity:
        return True
    else:
        return False


def imag_part(a):
    if is_infinity(a):
        return a
    try:
        return a.imag()
    except AttributeError:  # Infinity
        return a


def real_part(a):
    try:
        return a.real()
    except AttributeError:  # Infinity
        return a


def JtoP(H, MR, p=None):
    CC = MR.base_ring()
    RR = H.base_ring()
    I = CC.gen()
    if p is None:
        p = RR(17) / RR(5) * H.gen(1) - RR(1) / RR(2) * H.gen(0) + H(RR(1) / RR(3))
    pp = p.coefficient_tuple()
    a = CC(pp[:2])
    st = CC(pp[2]).sqrt()
    stinv = st**-1
    return MR([st, a * stinv, CC(0), stinv]), MR([stinv, -a * stinv, CC(0), st])


def act_H3(g, w):
    A, B, C, D = g.list()
    HH = w.parent()
    RR = HH.base_ring()
    gw = (A * w + B) * (C * w + D) ** -1
    sqrnormgw = sum(o**2 for o in gw.coefficient_tuple())
    assert not sqrnormgw < 0, "g = %s, w = %s\ngw = %s, sqrnorm = %s" % (
        g,
        w,
        gw,
        sqrnormgw,
    )
    if sqrnormgw >= 1:
        gw = gw / sqrnormgw.sqrt()
        gw *= HH(1 - RR(1) / RR(2) ** HH.base_ring().precision())
    return gw


def M2Z(v):
    return Matrix(ZZ, 2, 2, v)


def FGP_V(x):
    return x.V() if isinstance(x, FGP_Module_class) else x


def FGP_W(x):
    return x.W() if isinstance(x, FGP_Module_class) else x.zero_submodule()


def direct_sum_of_modules(v):
    V = reduce(lambda x, y: FGP_V(x).direct_sum(FGP_V(y)), v)
    V = V.ambient_module()
    W = V.submodule(matrix.block_diagonal([FGP_W(o).matrix() for o in v]))
    return V.quotient(W)


def direct_sum_of_maps(v):
    vv = [o.codomain() for o in v]
    V = (reduce(lambda x, y: FGP_V(x).direct_sum(FGP_V(y)), vv)).ambient_module()
    W = V.submodule(matrix.block_diagonal([FGP_W(o).matrix() for o in vv]))
    codomain = V.quotient(W)
    V = v[0].domain()
    try:
        imgens = [
            codomain(codomain.V()(sum([(f(g).lift()).list() for f in v], [])))
            for g in V.gens()
        ]
    except AttributeError:
        imgens = [
            codomain(codomain.V()(sum([f(g).list() for f in v], []))) for g in V.gens()
        ]
    return V.hom(imgens, codomain=codomain)


def is_in_principal_affinoid(p, z):
    if z.valuation() != 0:
        return False
    for i in range(p):
        if (z - z.parent()(i)).valuation() > 0:
            return False
    return True


def find_containing_affinoid(p, z, level=1):
    r"""
    Returns the vertex corresponding to the affinoid in
    the `p`-adic upper half plane that a given (unramified!) point reduces to.

    INPUT:

      - ``z`` - an element of an unramified extension of `\QQ_p` that is not contained
        in `\QQ_p`.

    OUTPUT:

      A 2x2 integer matrix representing the affinoid.

        sage: K.<a> = Qq(5^2,20)
        sage: from darmonpoints.util import find_containing_affinoid
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
    # Assume z belongs to some extension of the padics.
    if z.valuation(p) < 0:
        return M2Z([0, 1, p * level, 0]) * find_containing_affinoid(p, 1 / (p * z))
    a = 0
    pn = 1
    val = z.valuation(p)
    try:
        L = [0] * val + list(z.unit_part().expansion())
    except AttributeError:
        L = [0] * val + z.unit_part().list()
    for n in range(len(L)):
        if L[n] != 0:
            if len(L[n]) > 1:
                break
            if len(L[n]) > 0:
                a += pn * L[n][0]
        pn *= p
    return M2Z([pn, a, 0, 1])


def point_radius(z, level=1):
    r"""
    Returns the vertex corresponding to the affinoid in
    the `p`-adic upper half plane that a given (unramified!) point reduces to.

    INPUT:

      - ``z`` - an element of an unramified extension of `\QQ_p` that is not contained
        in `\QQ_p`.

    OUTPUT:

    """
    p = z.parent().prime()
    # Assume z belongs to some extension of the padics.
    if z.valuation(p) < 0:
        return 1 + point_radius(1 / (p * z))
    a = 0
    pn = 1
    ans = 0
    val = z.valuation(p)
    try:
        L = [0] * val + list(z.unit_part().expansion())
    except AttributeError:
        L = [0] * val + z.unit_part().list()
    for n in range(len(L)):
        if L[n] != 0:
            if len(L[n]) > 1:
                break
            if len(L[n]) > 0:
                a += pn * L[n][0]
        pn *= p
        ans += 1
    return ans


def find_center(p, level, t1, t2):
    r"""
    This function computes the center between two points in Cp
    """
    old_dir = M2Z([1, 0, 0, 1])
    E0inf = [M2Z([0, -1, level, 0])]
    E0Zp = [M2Z([p, a, 0, 1]) for a in range(p)]
    while True:
        new_dirs = [old_dir * e0 for e0 in E0Zp]
        same_ball = False
        new_dir = None
        for g in new_dirs:
            a, b, c, d = g.adjugate().list()
            # Check whether t1 and t2 are in the open given by g
            if all(
                [(a * t + b).valuation() >= (c * t + d).valuation() for t in [t1, t2]]
            ):
                new_dir = g
                break
        if new_dir is None:
            return old_dir
        else:
            old_dir = new_dir


def is_in_Gamma_1(mat, N, p=None, determinant_condition=True):
    if N != 1:
        a, b, c, d = mat.list()
        if p is None and not all([QQ(x).is_integral() for x in [a, b, c, d]]):
            return False
        if p is not None and not all([QQ(x).is_S_integral([p]) for x in [a, b, c, d]]):
            return False
        if Zmod(N)(a) != 1 or Zmod(N)(c) % N != 0:
            return False
    if determinant_condition and mat.determinant() != 1:
        return False
    return True


def is_in_Gamma0loc(A, det_condition=True, p=None):
    r"""
    Whether the matrix A has all entries Zp-integral, and is upper-triangular mod p.
    """
    if det_condition == True and A.determinant() != 1:
        return False
    if p is not None:
        return all(o.valuation(p) >= 0 for o in A.list()) and A[1, 0].valuation(p) > 0
    else:
        return all(o.valuation() >= 0 for o in A.list()) and A[1, 0].valuation() > 0


def set_immutable(x):
    try:
        x.set_immutable()
        return x
    except AttributeError:
        return x


def act_flt(g, x):
    a, b, c, d = g.list()
    K = x.parent()
    if x == Infinity:
        return a / c
    if K(c) * x + K(d) == 0:
        return Infinity
    else:
        return (K(a) * x + K(b)) / (K(c) * x + K(d))


def tate_parameter(E, R):
    p = R.prime()
    prec = R.precision_cap()
    jE = E.j_invariant()

    # Calculate the Tate parameter
    E4 = EisensteinForms(weight=4).basis()[0]
    Delta = CuspForms(weight=12).basis()[0]
    j = (E4.q_expansion(prec + 7)) ** 3 / Delta.q_expansion(prec + 7)
    qE = j.inverse().power_series().reverse()(R(1 / jE))
    return qE


def get_C_and_C2(E, qEpows, R, prec):
    sk3 = sk5 = 0
    n2 = n3 = 0
    for n in range(1, prec):
        rn = 1 / (1 - qEpows[n]) - 1
        n2 += 2 * n - 1
        n3 += 3 * n2 - 3 * n + 1
        newsk3 = n3 * rn
        sk3 += newsk3
        sk5 += n2 * newsk3
    tate_a4 = -5 * sk3
    tate_a6 = (tate_a4 - 7 * sk5) / 12
    Eqc4, Eqc6 = 1 - 48 * tate_a4, -1 + 72 * tate_a4 - 864 * tate_a6
    C2 = (R(Eqc4) * R(E.c6())) / (R(Eqc6) * R(E.c4()))
    return our_sqrt(R(C2), R), C2


def get_c4_and_c6(qE, prec):
    sk3 = sk5 = 0
    n2 = n3 = 0
    for n in range(1, prec):
        rn = 1 / (1 - qE**n) - 1
        n2 += 2 * n - 1
        n3 += 3 * n2 - 3 * n + 1
        newsk3 = n3 * rn
        sk3 += newsk3
        sk5 += n2 * newsk3
    tate_a4 = -5 * sk3
    tate_a6 = (tate_a4 - 7 * sk5) / 12
    Eqc4, Eqc6 = 1 - 48 * tate_a4, -1 + 72 * tate_a4 - 864 * tate_a6
    return Eqc4, Eqc6


def get_j_invariant(qE, prec):
    E4 = EisensteinForms(weight=4).basis()[0]
    Delta = CuspForms(weight=12).basis()[0]
    j = (E4.q_expansion(prec + 7)) ** 3 / Delta.q_expansion(prec + 7)
    return j(qE)


def getcoords(E, u, prec=None, R=None, qE=None, qEpows=None, C=None):
    if R is None:
        R = u.parent()
        u = R(u)
    p = R.prime()
    if prec is None:
        prec = u.precision_relative()
    if qE is None:
        if qEpows is not None:
            qE = qEpows[1]
        else:
            jE = E.j_invariant()
            # Calculate the Tate parameter
            E4 = EisensteinForms(weight=4).basis()[0]
            Delta = CuspForms(weight=12).basis()[0]
            j = (E4.q_expansion(prec + 7)) ** 3 / Delta.q_expansion(prec + 7)
            qE = j.inverse().power_series().reverse()(R(1 / jE))

    qEval = qE.valuation()

    precn = (prec / qEval).floor() + 4
    precp = ((prec + 4) / qEval).floor() + 2
    qpow = -(u.valuation() / qEval).floor()

    if qEpows is None:
        qEpows = [R(1), qE]
        for i in range(abs(len(qEpows) - max([precn, precp + 1, qpow.abs()]))):
            qEpows.append(qE * qEpows[-1])
    if len(qEpows) < qpow.abs() + 1:
        for i in range(qpow.abs() + 1 - len(qEpows)):
            qEpows.append(qE * qEpows[-1])

    # Normalize the period by appropriate powers of qE
    if qpow >= 0:
        un = u * qEpows[qpow]
    else:
        un = u * qEpows[-qpow] ** -1

    if un == 1:
        return Infinity

    # formulas in Silverman II (Advanced Topics in the Arithmetic of Elliptic curves, p. 425)
    xx = un / (1 - un) ** 2
    yy = xx**2 * (1 - un)  # = un**2/(1-un)**3
    for n in range(1, precn):
        qEn = qEpows[n]
        qEn_times_un = qEn * un
        first_sum = qEn_times_un / (1 - qEn_times_un) ** 2
        second_sum = first_sum**2 * (1 - qEn_times_un)
        den_un = 1 - qEn / un
        den_un_2 = den_un**2
        qEn_over_un_den_un_2 = qEn / (un * den_un_2)
        rat = qEn / (1 - qEn) ** 2
        xx += first_sum + qEn_over_un_den_un_2 - 2 * rat
        yy += second_sum - qEn_over_un_den_un_2 / den_un + rat

    if C is None:
        C, C2 = get_C_and_C2(E, qEpows, R, precp + 1)
    else:
        C2 = C**2

    s = (C - R(E.a1())) / R(2)
    r = (s * (C - s) - R(E.a2())) / 3
    t = (r * (2 * s - C) - R(E.a3())) / 2
    return (r + C2 * xx, t + s * C2 * xx + C * C2 * yy)


def period_from_coords(R, E, P, prec=20, K_to_Cp=None):
    r"""
    Given a point `P` in the formal group of the elliptic curve `E` with split multiplicative reduction,
    this produces an element `u` in `\QQ_p^{\times}` mapped to the point `P` by the Tate parametrisation.
    The algorithm return the unique such element in `1+p\ZZ_p`.

    INPUT:

    - ``P`` - a point on the elliptic curve.

    - ``prec`` - the `p`-adic precision, default is 20.

    """
    p = R.prime()
    jE = E.j_invariant()
    if K_to_Cp is None:
        K_to_Cp = lambda x: x

    # Calculate the Tate parameter
    E4 = EisensteinForms(weight=4).basis()[0]
    Delta = CuspForms(weight=12).basis()[0]
    j = (E4.q_expansion(prec + 7)) ** 3 / Delta.q_expansion(prec + 7)
    qE = j.inverse().power_series().reverse()(R(1 / jE))
    sk = lambda q, k, pprec: sum(
        [n**k * q**n / (1 - q**n) for n in range(1, pprec + 1)]
    )
    n = qE.valuation()
    precp = ((prec + 4) / n).floor() + 2
    tate_a4 = -5 * sk(qE, 3, precp)
    tate_a6 = (tate_a4 - 7 * sk(qE, 5, precp)) / 12
    Eq = EllipticCurve(
        [R(1), R(0), R(0), tate_a4, tate_a6]
    )  # y^2 + xy = x^3 + a4x + a6

    C2 = (Eq.c6() * R(E.c4())) / (Eq.c4() * R(E.c6()))
    C = our_sqrt(R(C2), R)  # .square_root()
    s = (C * R(E.a1()) - R(1)) / R(2)
    r = (C**2 * R(E.a2()) + s + s**2) / R(3)
    t = (C**3 * R(E.a3()) - r) / R(2)
    xx = r + C**2 * K_to_Cp(P[0])
    yy = t + s * C**2 * K_to_Cp(P[0]) + C**3 * K_to_Cp(P[1])

    tt = -xx / yy
    if tt.valuation(p) <= 0:
        raise ValueError(
            "The point must lie in the formal group (valuation = %s should be positive)."
            % tt.valuation(p)
        )

    eqhat = Eq.formal()
    eqlog = eqhat.log(prec + 3)
    z = eqlog(tt)
    u = ZZ(1)
    fac = ZZ(1)
    for i in range(1, 2 * prec + 1):
        fac = fac * i
        u = u + z**i / fac
    un = u * qE ** (-(u.valuation() / qE.valuation()).floor())
    return un


def our_lindep(V, prec=None, base=None):
    if base is None:
        K = V[0].parent()
    else:
        K = base
    V = [K(o) for o in V]
    if prec is None:
        prec = min([o.precision_absolute() for o in V])
    field_deg = K.degree()
    p = K.prime()
    pn = p**prec
    n = len(V)
    M = matrix(ZZ, n + field_deg, field_deg)
    for k in range(n):
        r = V[k]
        if field_deg == 1:
            M[k, 0] = ZZ(r.lift()) % pn
        else:
            for j, o in enumerate(r.expansion()):
                for i, u in enumerate(o):
                    M[k, -1 - i] += (p ** (j + r.valuation()) * u) % pn
    for i in range(field_deg):
        M[n + i, -1 - i] = pn
    verb_lev = get_verbose()
    set_verbose(0)
    tmp = (
        M.transpose()
        .change_ring(ZZ)
        .right_kernel_matrix(proof=False, algorithm="flint")
    )
    set_verbose(verb_lev)
    tmp = tmp.LLL().row(0)
    return list(tmp)[:n]


def our_algdep(z, degree, prec=None):
    if prec is None:
        prec = z.precision_relative()
    field_deg = z.parent().degree()
    p = z.parent().prime()
    pn = p**prec
    R = PolynomialRing(ZZ, names="x")
    RQ = PolynomialRing(QQ, names="y")
    x = R.gen()
    n = degree + 1
    zval = z.valuation()
    ptozval = p**zval
    z /= ptozval
    assert z.valuation() == 0
    r = 1
    M = matrix(ZZ, n + field_deg, field_deg)
    M[0, -1] = 1  # Encodes 1
    for k in range(1, degree + 1):
        r *= z
        if field_deg == 1:
            M[k, 0] = ZZ(r.lift()) % pn
        else:
            for j, o in enumerate(r.expansion()):
                for i, u in enumerate(o):
                    M[k, -1 - i] += (p**j * u) % pn
    for i in range(field_deg):
        M[n + i, -1 - i] = pn
    verb_lev = get_verbose()
    set_verbose(0)
    tmp = M.transpose().right_kernel_matrix().change_ring(ZZ).LLL().row(0)
    set_verbose(verb_lev)
    f = RQ(list(tmp[:n]))(x / ptozval)
    if f.leading_coefficient() < 0:
        f = -f
    ans = R(f.denominator() * f)
    for fact, _ in ans.factor():
        if R(fact)(z).valuation() >= prec:
            return R(fact / fact.content())
    return R(ans / ans.content())


def lift_padic_splitting(a, b, II0, JJ0, p, prec):
    R = a.parent()  # Qp(p,prec)
    # II0,JJ0,_ = Q.modp_splitting_data(p)
    II0 = II0.apply_map(lambda o: R(o.lift()))
    II0[1, 1] = -II0[0, 0]
    JJ0 = JJ0.apply_map(lambda o: R(o.lift()))
    JJ0[1, 1] = -JJ0[0, 0]
    oldII = None
    oldJJ = None
    newII = II0
    newJJ = JJ0
    n_iters = 0
    current_prec = -1
    while current_prec < prec:  # newII != oldII or newJJ != oldJJ:
        n_iters += 1
        oldII, oldJJ = newII, newJJ
        x1, x2, x3, _ = oldII.list()
        y1, y2, y3, _ = oldJJ.list()
        n = min(
            o.valuation()
            for o in [
                x1**2 + x2 * x3 - a,
                y1**2 + y2 * y3 - b,
                2 * x1 * y1 + x2 * y3 + x3 * y2,
            ]
        )
        verbose("current_prec = %s" % n)
        x1, x2, x3, _ = (o.lift() for o in oldII.list())
        y1, y2, y3, _ = (o.lift() for o in oldJJ.list())
        B = matrix(
            R,
            3,
            6,
            [
                2 * x1,
                x3,
                x2,
                0,
                0,
                0,
                0,
                0,
                0,
                2 * y1,
                y3,
                y2,
                2 * y1,
                y3,
                y2,
                2 * x1,
                x3,
                x2,
            ],
        )
        pn = p**n
        A = -matrix(
            R,
            3,
            1,
            [
                ZZ((x1**2 + x2 * x3 - a) / pn),
                ZZ((y1**2 + y2 * y3 - b) / pn),
                ZZ((2 * x1 * y1 + x2 * y3 + x3 * y2) / pn),
            ],
        )
        delta = B.solve_right(A)
        x1, x2, x3, y1, y2, y3 = delta.list()
        newII = oldII + pn * matrix(R, 2, 2, [x1, x2, x3, -x1])
        newJJ = oldJJ + pn * matrix(R, 2, 2, [y1, y2, y3, -y1])
        current_prec = n
        if n_iters > 2 * prec:
            raise RuntimeError("Hensel iteration does not seem to converge")
    R = Qp(p, prec)
    return newII.change_ring(R), newJJ.change_ring(R)


def polynomial_roots(f, K):
    r"""
    Finds the roots of f in the field K, using Hensel lift.

    TESTS::

        sage: from darmonpoints.util import polynomial_roots
        sage: x = QQ['x'].gen()
        sage: K.<g> = Qp(5,20).extension(x^2-x-13)
        sage: f = x^8 - 576*x^6 + 86568*x^4 - 731648*x^2 + 3283344
        sage: alpha = polynomial_roots(f, K)[0]
        sage: alpha.precision_absolute()
        20
        sage: f(alpha)
        O(5^20)
    """

    return [o for o, _ in f.change_ring(K).roots()]


def polynomial_roots_old(f, K):
    ans = []
    p = K.prime()
    rng = range(2 * p) if p > 2 else range(8)  # DEBUG: why do we need the 2*p??
    for rvec in product(rng, repeat=K.degree()):
        r = sum(r0 * K.gen() ** i for i, r0 in enumerate(rvec))
        try:
            rt = hensel_lift(f, r)
            if f(rt).valuation() < K.precision_cap() // 2:  # DEBUG!!
                raise RuntimeError(
                    "Couln't reach target valuation (%s), got only %s"
                    % (K.precision_cap(), f(rt).valuation())
                )
            ans.append(rt)
        except ValueError:
            pass
    return ans


# use hensel lemma to lift an approximate root x0 of the polynomial f to a root to the desired precision
def hensel_lift(f, x0, max_iters=None):
    xn = x0
    n_iters = 0
    fder = f.derivative()
    if max_iters is None:
        max_iters = 1 + RR(x0.parent().precision_cap()).log(2).ceiling()
    if f(xn).valuation() <= 2 * fder(xn).valuation():
        raise ValueError("Approximation is not good enough")
    while n_iters < max_iters:
        n_iters += 1
        xnn = xn - f(xn) / fder(xn)
        if xn == xnn:
            return xn
        xn = xnn
    raise RuntimeError("Does not seem to converge")


# Returns the change of coordinates function resulting of sending
# x1p |-> oo
# x2p |-> 0
# x3p |-> 1
def affine_transformation(x1p, x2p, x3p):
    return lambda x: (x - x2p) * (x3p - x1p) / ((x - x1p) * (x3p - x2p))


def height_polynomial(x, base=10):
    return sum((RR(o).abs() + 1).log(base) for o in x.coefficients())


def recognize_DV_algdep(
    J,
    degree,
    height_threshold=None,
    prime_bound=None,
    roots_of_unity=None,
    outfile=None,
):
    K = J.parent()
    p = K.prime()
    if prime_bound is None:
        prime_bound = max(1000, min((K.precision_cap() ** p) // 4, 100000))
    B = prime_range(prime_bound)
    if roots_of_unity is None:
        roots_of_unity = our_nroot(K(1), lcm(12, (p**2 - 1)), return_all=True)
    if height_threshold is None:
        height_threshold = 0.9 * K.precision_cap() * degree
    for i, zz in enumerate(roots_of_unity):
        Jz = J * zz
        ff = our_algdep(Jz, degree)
        height_poly = height_polynomial(ff, base=p)
        if height_poly < height_threshold:
            disc = QQ(ff.discriminant())
            # print("%s (disc=%s)\t (J * z^%s\t (height=%s)"%(ff.factor(), disc, i, height_polynomial(ff, base=p)))
            if disc.prime_to_S_part(B).abs() == 1:
                fwrite("# SUCCESS!", outfile)
                fwrite(
                    "# %s (disc=%s)\t (J * exp(2 pi i %s / %s\t (height=%s)"
                    % (
                        ff.factor(),
                        disc.factor(),
                        i,
                        lcm(12, (p**2 - 1)),
                        height_polynomial(ff, base=p),
                    ),
                    outfile,
                )
                fwrite("x = QQ['x'].gen()", outfile)
                fwrite("f = %s" % ff, outfile)
                return Jz, ff
    return None, None


def recognize_DV_lindep(
    J, M, prime_list, Cp=None, units=None, extra_periods=None, outfile=None, **kwargs
):
    r"""
    TESTS::

        sage: from darmonpoints.util import recognize_DV_lindep
        sage: x = QQ['x'].gen()
        sage: K.<g> = Qp(3, 50).extension(x^2 - x - 13)
        sage: J = 2263329212681251489468 + 6644010739654744556634*g + O(3^46)
        sage: M.<a> = NumberField(x^8 - 576*x^6 + 86568*x^4 - 731648*x^2 + 3283344)
        sage: Jrec = recognize_DV_lindep(J, M, [2,23,31], algebraic=True)[0]
        # SUCCESS!
        ...

    """
    if extra_periods is None:
        extra_periods = []
    K = J.parent()
    p = K.prime()
    prec = J.precision_absolute()
    # embed M in a field containing K
    if Cp is None:
        Cp = K
        K_to_Cp = K.hom([K.gen()])
    else:
        K_to_Cp = K.hom([polynomial_roots(K._exact_modulus(), Cp)[0]])
    debug_idx = kwargs.pop("debug_idx", 0)
    embeddings = polynomial_roots(M.polynomial(), Cp)
    if len(embeddings) == 0:
        raise ValueError(f"M (={M}) does not embed into Cp (={Cp})")
    phi = kwargs.pop("phi", None)
    if phi is None:
        phi_list = []
        for rt in embeddings:
            phi = M.hom([rt])
            xp = phi(M.gen())
            xpconj = xp.trace() - xp
            # We find sigma in Gal(M) such that it corresponds to conjugation in Cp.
            found = False
            for sigma in M.automorphisms():
                if xpconj == phi(sigma(M.gen())):
                    found = True
                    break
            if found:
                phi_list.append((phi, sigma))
        try:
            phi, sigma = phi_list[debug_idx]
        except IndexError:
            raise ValueError(
                f"There are only {len(phi_list)} embeddings but debug_idx is {debug_idx}"
            )
    V = [None]
    Vlogs = [K_to_Cp(J.log(0))]
    W = ["J"]
    class_number = kwargs.get("class_number", None)
    if class_number is not None:
        for ell in prime_list:
            ell_set = set([])
            for pp, _ in M.ideal(ell).factor():
                verbose(f"(Factoring {ell})")
                gens = (pp**class_number).gens_reduced(proof=False)
                assert (
                    len(gens) == 1
                ), f"Wrong class number ( = {class_number}). Witness: {ell}"
                if phi(gens[0]).valuation() == 0:
                    ell_set.add(gens[0])
            while ell_set:
                g0 = ell_set.pop()
                sg0 = sigma(g0)
                g1_list = [g1 for g1 in ell_set if sg0 in M.ideal(g1)]
                assert len(g1_list) <= 1
                if len(g1_list) == 0:
                    V.append(g0)
                    Vlogs.append(phi(g0).log(0))
                    W.append(ell)
                elif len(g1_list) == 1:
                    ell_set.remove(g1_list[0])
                    quot = g0 / g1_list[0]
                    V.append(quot)
                    Vlogs.append(phi(quot).log(0))
                    W.append(ell)
    else:
        hMlist = [1]
        for ell in prime_list:
            for pp, _ in M.ideal(ell).factor():
                verbose(f"(Factoring {ell}")
                hM = 0
                gens = [None, None]
                while len(gens) > 1:
                    hM += 1
                    gens = (pp**hM).gens_reduced(proof=False)
                gens0 = gens[0]
                phiv = phi(gens0)
                if phiv.valuation() == 0:
                    hMlist.append(hM)
                    V.append(gens0)
                    Vlogs.append(phiv.log(0))
                    W.append(ell)
        hM = lcm(hMlist)
        assert len(V) == len(hMlist)
        V = [None] + [o ** (hM / e) for o, e in zip(V[1:], hMlist[1:])]
        Vlogs = [Vlogs[0]] + [(hM / e) * o for o, e in zip(Vlogs[1:], hMlist[1:])]

    # Add units
    if units is None:
        units = list(M.units(proof=False))
    else:
        units = [M(o) for o in units]
    for i, u in enumerate(units):
        V.append(u)
        Vlogs.append(phi(u).log(0))
        W.append(f"u{i}")

    # Add extra periods
    for i, per in enumerate(extra_periods):
        Vlogs.append(K_to_Cp(per.log(0)))
        W.append(f"period_{i}")

    # Truncate precision if prec is specified
    prec = kwargs.get("prec", prec)
    if prec is not None:
        Vlogs = [o.add_bigoh(prec) for o in Vlogs]

    # OK now cross fingers...
    clist = kwargs.get("clist", None)
    if clist is not None:
        assert len(clist) == len(
            Vlogs
        ), f"Provided clist is of incorrect length (should be {len(Vlogs)})"
        return sum([c * o for c, o in zip(clist, Vlogs)])
    clist = our_lindep(Vlogs)
    verbose(f"clist = {clist}")
    verbose(f"W = {W}")
    verbose(f"Should be zero : {sum([c * o for c, o in zip(clist, Vlogs)])}")
    if clist[0] < 0:
        clist = [-o for o in clist]
    if clist[0] == 0:
        verbose(f"Not recognized: clist[0] = {clist[0]}")
        return None
    ht = 2 * sum((1 + RR(o).abs()).log(p) for o in clist)
    verbose(f"(confidence factor: { ht / prec})")
    if ht > prec:
        verbose(
            f"Not recognized (confidence factor: ht / prec = {ht / prec}): clist = {clist}"
        )
        return None
    clist_ans = [(u, v) for u, v in zip(clist, W) if u != 0]
    fwrite("# SUCCESS!", outfile)
    fwrite(f"# {clist_ans}", outfile)
    algebraic = kwargs.get("algebraic", True)
    if not algebraic:
        return clist_ans
    else:
        verbose(str(clist_ans))
        if not clist[0] > 0:
            verbose(f"Redundant set of primes?")
            return None
        fact = Factorization([(u, -a) for u, a in zip(V[1:], clist[1:])])
        assert len(V) + len(extra_periods) == len(clist)
        # assert clist[0] % hM == 0
        hM = 1  # DEBUG
        J_alg = fact.prod()  # DEBUG # (M['x'].gen()**hM - fact.prod()).roots(M)[0][0]
        remainder = clist[0] // hM
        try:
            check = (phi(J_alg) / K_to_Cp(J) ** remainder).log(0) == 0
            if not check:
                print("Did not pass check! Returning value anyway...")
        except ValueError as e:
            print("Did not pass check because it errored! (error = %s)" % str(e))
        return (
            J_alg,
            remainder,
            fact,
            clist_ans,
        )  # DEBUG - didn't check that they match...


def recognize_point(x, y, E, F, prec=None, HCF=None, E_over_HCF=None):
    hF = F.class_number()
    if HCF is None:
        if hF > 1:
            HCF = F.hilbert_class_field(names="r1")
        else:
            HCF = F
    Cp = x.parent()
    s = F.gen()
    w = F.maximal_order().ring_generators()[0]
    # assert w.minpoly()(Cp.gen()) == 0
    Floc = Cp.base_ring()
    p = Cp.prime()
    if prec is None:
        prec = Floc.precision_cap()
    if x == 0 and y == 0:
        list_candidate_x = [0]
    elif (1 / x).valuation() > prec and (1 / y).valuation() > prec:
        if E_over_HCF is not None:
            return E_over_HCF(0), True
        else:
            return E.change_ring(HCF)(0), True
    elif E.base_ring() == QQ and hF == 1:
        # We need to ensure that w and g are compatible
        wp = polynomial_roots(w.minpoly(), Cp)[0]
        # assert w.minpoly()(Cp.gen()) == 0
        x1 = 0
        x2 = 0
        for i, o in enumerate(x.expansion()):
            if len(o) > 0:
                x1 += o[0] * p**i
            if len(o) > 1:
                x2 += o[1] * p**i
        u = 0
        v = 0
        for i, o in enumerate(wp.expansion()):
            if len(o) > 0:
                u += o[0] * p**i
            if len(o) > 1:
                v += o[1] * p**i

        u = (p ** wp.valuation()) * Floc(u).add_bigoh(prec)
        v = (p ** wp.valuation()) * Floc(v).add_bigoh(prec)
        u = QQ(u)
        v = QQ(v)
        # wrote wp = u + g * v
        x1 = (p ** x.valuation()) * Floc(x1).add_bigoh(prec)
        x2 = (p ** x.valuation()) * Floc(x2).add_bigoh(prec)
        x1 = QQ(x1)
        x2 = QQ(x2)
        list_candidate_x = [x1 + x2 * w]  # [x1 - x2 * u / v + (x2 / v) * w] # DEBUG
    else:
        candidate_x = our_algdep(x, E.base_ring().degree() * 2 * hF, prec)
        pol_height = height_polynomial(candidate_x, base=p)
        if pol_height < 0.9 * prec:  # .9 is quite arbitrary...
            list_candidate_x = [rt for rt, pw in candidate_x.change_ring(HCF).roots()]
        else:
            list_candidate_x = []
    if len(list_candidate_x) > 0:
        if E_over_HCF is None:
            E_over_HCF = E.change_ring(HCF)
        for candidate_x in list_candidate_x:
            try:
                Pt = E_over_HCF.lift_x(candidate_x)
                if Pt.is_finite_order():  # DEBUG
                    raise ValueError
                verbose("Point is in curve: %s" % Pt, level=2)
                return Pt, True
            except ValueError:
                verbose("Point does not appear to lie on curve...", level=2)
    return candidate_x, False


def solve_quadratic(f, K=None, return_all=False):
    a, b, c = f[2], f[1], f[0]
    if f.degree() != 2:
        raise ValueError
    disc = b * b - 4 * a * c
    discrt = our_sqrt(disc, K, False)
    if return_all:
        return [(-b + discrt) / (2 * a), (-b - discrt) / (2 * a)]
    else:
        return (-b + discrt) / (2 * a)


def our_sqrt(xx, K=None, return_all=False):
    if K is None:
        K = xx.parent()
    else:
        xx = K(xx)
    if xx == 0:
        if return_all:
            return [xx]
        else:
            return xx
    p = K.base_ring().prime()
    prec = K.precision_cap()
    valp = xx.valuation()
    valpi = xx.ordp()
    try:
        eK = K.ramification_index()
    except AttributeError:
        eK = 1
    if valp * eK % 2 != 0:
        if return_all:
            return []
        else:
            raise ValueError("Not a square")
    x = K.uniformizer() ** (-valp) * xx
    try:
        z = K.unramified_generator()
    except AttributeError:
        z = K.gen()
    deg = K.residue_class_field().degree()
    found = False
    if p != 2:
        ppow = p if p != 2 else 8
        minval = 1 if p != 2 else 3
        for avec in product(range(ppow), repeat=deg):
            y0 = K(avec[0])
            for a in avec[1:]:
                y0 = y0 * z + K(a)
            if (y0**2 - x).valuation() >= minval:
                found = True
                break
        if found == False:
            if return_all:
                return []
            else:
                raise ValueError("Not a square: %s" % x)
        y, y1 = 0, y0
        while y != y1:
            y, y1 = y1, (y1 + x / y1) / 2
    else:
        ppow = 8
        minval = 1
        for avec in product(range(ppow), repeat=deg):
            y0 = K(avec[0])
            for a in avec[1:]:
                y0 = y0 * z + K(a)
            if (y0**2 - y0 + (1 - x) / 4).valuation() >= minval:
                found = True
                break
        if found == False:
            if return_all:
                return []
            else:
                raise ValueError("Not a square: %s" % x)
        y, y1 = 0, y0
        while y != y1:
            y, y1 = y1, (y1**2 - (1 - x) / 4) / (2 * y1 - 1)  # (y1+x/y1)/2
        y = 2 * y - 1
    ans = K.uniformizer() ** (ZZ(valp / 2)) * y
    assert ans**2 == xx
    if return_all:
        ans = [ans, -ans]
    return ans


def our_cuberoot(xx, K=None, return_all=False):
    if K is None:
        K = xx.parent()
    if xx == 0:
        if return_all:
            return [xx]
        else:
            return xx
    xx = K(xx)
    p = K.base_ring().prime()
    prec = K.precision_cap()
    valp = xx.valuation()
    try:
        eK = K.ramification_index()
    except AttributeError:
        eK = 1
    valpi = eK * valp
    if valpi % 3 != 0:
        raise ValueError("Not a cube")
    x = K.uniformizer() ** (-valp) * xx
    try:
        z = K.unramified_generator()
    except AttributeError:
        z = K.gen()
    deg = K.residue_class_field().degree()
    found = False
    ppow = p if p != 3 else 9
    minval = 1 if p != 3 else 2
    if deg == 1:
        for y0 in range(ppow):
            if (K(y0) ** 3 - x).valuation() >= minval:
                found = True
                break
    else:
        for avec in product(range(ppow), repeat=deg):
            y0 = K(0)
            for a in avec:
                y0 *= z
                y0 += K(a)
            if (y0**3 - x).valuation() >= minval:
                found = True
                break
    if found == False:
        raise ValueError("Not a cube")
    y1 = y0
    y = K(0)
    num_iters = 0
    while y != y1 and num_iters < 2 * prec:
        y = y1
        y2 = y**2
        y1 = (2 * y * y2 + x) / (3 * y2)
    ans = K.uniformizer() ** (ZZ(valpi / 3)) * y
    if return_all:
        cubicpol = PolynomialRing(K, "t")([1, 1, 1])
        ans = [ans] + [K(o) * ans for o, _ in cubicpol.roots()]
    return ans


def our_nroot(xx, n, K=None, return_all=False):
    if K is None:
        K = xx.parent()
    if xx == 0:
        if return_all:
            return [xx]
        else:
            return xx
    n = ZZ(n)
    xx = K(xx)
    if n == 1:
        return [xx] if return_all else xx
    elif n == -1:
        return [xx**-1] if return_all else xx ** -1
    sgn = n.sign()
    n = n.abs()
    p = K.base_ring().prime()
    prec = K.precision_cap()
    valp = xx.valuation()
    valpi = xx.ordp()
    try:
        eK = K.ramification_index()
    except AttributeError:
        eK = 1
    if valp * eK % n != 0:
        if return_all:
            return []
        else:
            raise ValueError("Not an n-th power")
    x = K.uniformizer() ** (-valp) * xx
    try:
        z = K.unramified_generator()
    except AttributeError:
        z = K.gen()
    deg = K.residue_class_field().degree()
    found = False
    try:
        z = K.unramified_generator()
    except AttributeError:
        z = K.gen()
    deg = K.residue_class_field().degree()
    if n % p == 0:
        minval = 3 if p == 2 else 2
    else:
        minval = 1
    ppow = p**minval
    y0list = []
    if deg == 1:
        for y0 in range(ppow):
            if (y0**n - x).valuation() >= minval and y0 not in y0list:
                y0list.append(y0)
                if not return_all:
                    break
    else:
        for avec in product(range(ppow), repeat=deg):
            y0 = avec[0]
            for a in avec[1:]:
                y0 = y0 * z + a
            if (y0**n - x).valuation() >= minval and y0 not in y0list:
                y0list.append(y0)
                if not return_all:
                    break
    if len(y0list) == 0 and not return_all:
        raise ValueError("Not an n-th power")
    ans_list = []
    for y0 in y0list:
        y1 = y0
        y = 0
        num_iters = 0
        while y != y1 and num_iters < 2 * prec:
            num_iters += 1
            y = y1
            yn = y**n
            y1 = ((n - 1) * yn + x) * y / (n * yn)
        ans = K.uniformizer() ** (ZZ(valp / n)) * y
        if sgn == 1:
            if ans not in ans_list:
                ans_list.append(ans)
        else:
            ansinv = ans**-1
            if ansinv not in ans_list:
                ans_list.append(ansinv)
    if return_all:
        return ans_list
    else:
        return ans_list[0]


def enumerate_words(v, n=None, max_length=-1):
    if n is None:
        n = []
    while True:
        yield [v[x] for x in n]
        add_new = True
        for jj in range(len(n)):
            n[jj] += 1
            if n[jj] != len(v):
                add_new = False
                break
            else:
                n[jj] = 0
        if add_new:
            if max_length == -1 or len(n) < max_length:
                n.append(0)
            else:
                raise StopIteration


def cantor_diagonal(iter1, iter2):
    v1 = [next(iter1)]
    v2 = [next(iter2)]
    while True:
        yield from zip(v1, v2)
        v1.append(next(iter1))
        v2.insert(0, next(iter2))


def act_flt_in_disc(g, x, P):
    Pconj = P.conjugate()
    z = (Pconj * x - P) / (x - 1)
    z1 = (g[0, 0] * z + g[0, 1]) / (g[1, 0] * z + g[1, 1])
    return (z1 - P) / (z1 - Pconj)


def translate_into_twosided_list(V):
    vp, vm = V
    return [None] + vp + list(reversed(vm))


def multiply_out(word, genlist, z=1):
    ans = z
    for i in word:
        if i > 0:
            ans = ans * genlist[i - 1]
        else:
            ans = ans * genlist[-i - 1] ** -1
    return ans


def tietze_to_syllables(wd):
    r"""
    Converts a word in Magma format into our own format.

    TESTS:

        sage: from darmonpoints.util import tietze_to_syllables
        sage: short = tietze_to_syllables([1,1,-3,-3,-3,2,2,2,2,2,-1,-1,-1]); short
        [(0, 2), (2, -3), (1, 5), (0, -3)]
    """
    return [
        (a - 1, len(list(g))) if a > 0 else (-a - 1, -len(list(g)))
        for a, g in groupby(wd)
    ]


def syllables_to_tietze(wd):
    return [sgn(a) * (i + 1) for i, a in wd for _ in range(abs(a))]


def reduce_word_tietze(word):
    r"""
    Simplifies the given word by cancelling out [g, -g] -> []
    """
    new_word = [i for i in word]
    old_word = []
    changed = True
    while changed:
        changed = False
        old_word = new_word
        for i in range(len(old_word) - 1):
            if old_word[i] == -old_word[i + 1]:
                changed = True
                new_word = old_word[:i] + old_word[i + 2 :]
                break
    return new_word


def reduce_word(word):
    r"""
    Simplifies the given word by cancelling out [g^a, g^b] -> [g^(a+b)],
    and [g^0] -> []
    """
    new_word = [(g, a) for g, a in word if a != 0]
    old_word = []
    changed = True
    while changed:
        changed = False
        old_word = new_word
        for i in range(len(old_word) - 1):
            if old_word[i][0] == old_word[i + 1][0]:
                changed = True
                new_exp = old_word[i][1] + old_word[i + 1][1]
                if new_exp != 0:
                    new_word = (
                        old_word[:i] + [(old_word[i][0], new_exp)] + old_word[i + 2 :]
                    )
                else:
                    new_word = old_word[:i] + old_word[i + 2 :]
                break
    return new_word


def get_heegner_params(p, E, beta):
    F = E.base_ring()
    if F == QQ:
        return _get_heegner_params_rational(p, E.conductor(), beta)
    else:
        return _get_heegner_params_numberfield(p, E.conductor(), beta)


def _get_heegner_params_numberfield(P, N, beta):
    F = N.number_field()
    x = PolynomialRing(F, names="x").gen()
    K = F.extension(x * x - beta, names="b")
    if not P.divides(N):
        raise ValueError("p (=%s) must divide conductor (=%s)" % (P, N))
    PK = K.ideal(P)
    if len(PK.factor()) > 1:
        raise ValueError("p (=%s) must be inert in K (=Q(sqrt{%s}))" % (P, beta))
    PK = PK.factor()[
        0
    ]  #    if PK.relative_ramification_index() > 1 or not PK.is_prime():
    N1 = N / P
    if P.divides(N1):
        raise ValueError("p (=%s) must exactly divide the conductor (=%s)" % (p, N))
    DB = F.ideal(1)
    Np = F.ideal(1)
    num_inert_primes = 0
    for ell, r in N1.factor():
        LK = K.ideal(ell)
        LKfact = LK.factor()
        # assert LK.relative_ramification_index() == 1
        if len(LKfact) == 1:  # inert or ramified
            if LKfact[0][1] == 1:  # inert
                num_inert_primes += 1
                DB *= ell**1
            else:  # ramified
                assert r == 1
                Np *= ell
        else:
            Np *= ell**r
    assert N == P * DB * Np
    inert_primes_at_infty = K.signature()[1] - 2 * F.signature()[1]
    if (inert_primes_at_infty + num_inert_primes) % 2 != 0:
        raise ValueError(
            "There should an even number of primes different than p which are inert"
        )
    return DB, Np, None


def _get_heegner_params_rational(p, N, beta):
    if N % p != 0:
        raise ValueError("p (=%s) must divide conductor (=%s)" % (p, N))
    if ZZ(beta).kronecker(p) != -1:
        raise ValueError("p (=%s) must be inert in K (=Q(sqrt{%s}))" % (p, beta))
    N1 = ZZ(N / p)
    if N1 % p == 0:
        raise ValueError("p (=%s) must exactly divide the conductor (=%s)" % (p, N))
    DB = 1
    Np = 1
    Ncartan = None
    num_inert_semistable_primes = 0
    for ell, r in N1.factor():
        ks = ZZ(beta).kronecker(ell)
        if ks == -1 or ks == 0:  # inert # DEBUG - or ramified!!!
            if r != 1:
                if r > 2:
                    raise ValueError(
                        "The inert prime l = %s divides too much the conductor." % ell
                    )
                if Ncartan is not None:
                    raise ValueError("Too many non-semistable primes")
                Ncartan = ell
            else:
                num_inert_semistable_primes += 1
                DB *= ell
        else:  # split or ramified
            Np *= ell**r
    if num_inert_semistable_primes % 2 != 0:
        raise ValueError(
            "There should an even number of primes different than p which are inert"
        )
    return DB, Np, Ncartan


def fwrite(string, outfile, newline=True):
    if outfile is None:
        fout = sys.stdout
        if newline:
            fout.write(string + "\n")
        else:
            fout.write(string)
    else:
        with open(outfile, "a") as fout:
            if newline:
                fout.write(string + "\n")
            else:
                fout.write(string)
        return


@cached_function
def module_generators_new(K):
    F = K.base_field()
    if F == QQ:
        return [1, K.maximal_order().ring_generators()[0]]
    OK = K.maximal_order()
    OF = F.maximal_order()
    r = OF.ring_generators()[0]
    w = OK.ring_generators()[0]
    OKbasis = OK.basis()
    A = matrix([w.coordinates_in_terms_of_powers()(o) for o in OKbasis])
    det1 = A.determinant().abs()
    for coeffs in sorted(
        product(range(-10, 10), repeat=4), key=lambda x: max(ZZ(o).abs() for o in x)
    ):
        g = sum((c * wi for c, wi in zip(coeffs, OKbasis)), K(1))
        det = (
            matrix([w.coordinates_in_terms_of_powers()(o) for o in [1, r, g, K(r) * g]])
            .determinant()
            .abs()
        )
        if det1 == det:
            return [1, g]


@cached_function
def module_generators(K):
    x = var("x")
    y = var("y")
    F = K.base_field()
    if F == QQ:
        return [1, K.maximal_order().ring_generators()[0]]
    f = F.polynomial()
    a = F.gen()
    g = K.relative_polynomial()
    b = K.gen()

    # Equivalent pari objects
    FP = F.pari_bnf().subst(x, y)
    fP = pari(f)
    KP = K.pari_rnf()
    gP = KP[0]
    BP = gp.rnfhnfbasis(FP, gP)

    E = [
        gp.matbasistoalg(FP, BP.vecextract(1)).lift(),
        gp.matbasistoalg(FP, BP.vecextract(2)).lift(),
    ]

    A = Matrix(F, 2, 2, 0)
    for jj in range(2):
        for ii in [1, 2]:
            tmp = E[jj][ii, 1].Vec().sage()
            if len(tmp) == 2:
                A[ii - 1, jj] = tmp[0] * a + tmp[1]
            else:
                A[ii - 1, jj] = tmp[0]
    return (Matrix(K, 1, 2, [1, b]) * A).list()


def find_the_unit_of(F, K):
    found = False
    GK = K.unit_group()
    OK = K.maximal_order()
    for uK in GK.fundamental_units():
        try:
            is_square, rootNuK = uK.norm(F).is_square(root=True)
        except TypeError:
            is_square = uK.norm(F).is_square()
            if is_square:
                rootNuK = uK.norm(F).sqrt()
            else:
                rootNuK = None
        if uK not in F:
            unit_not_in_F = uK
        if is_square and uK not in F:
            ans = uK / rootNuK
            unit_not_in_F = OK(ans)
            if (
                ans not in F
                and ans.multiplicative_order() == Infinity
                and ans.norm(F) == 1
            ):
                ans_inv = OK(1 / ans)  # just for testing
                return OK(ans)
    # Not found so far..
    norm = unit_not_in_F.norm(F)
    ans = unit_not_in_F**2 / norm
    assert ans not in F, "Expected unit not to be in F, but it is (= %s)" % ans
    assert ans.multiplicative_order() == Infinity, (
        "Expected unit to be nontorsion, but it is (= %s)" % ans
    )
    assert (
        ans.norm(F) == 1
    ), "Expected unit to be of relative norm 1, but it is not (= %s, Norm = %s)" % (
        ans,
        ans.norm(F),
    )
    ans_inv = OK(1 / ans)  # just for testing
    return OK(ans)


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


def sage_F_elt_to_magma(F_magma, x):
    return F_magma(x.list())


def quaternion_to_magma_quaternion(Bmagma, x):
    v = list(x)
    if v[0].parent() == QQ:
        return Bmagma(v[0]) + sum(v[i + 1] * Bmagma.gen(i + 1) for i in range(3))
    else:
        return sage_quaternion_to_magma(Bmagma, x)


def sage_quaternion_to_magma(B_magma, x):
    v = list(x.coefficient_tuple())
    return B_magma(sage_F_elt_to_magma(B_magma.BaseRing(), v[0])) + sum(
        sage_F_elt_to_magma(B_magma.BaseRing(), v[i + 1]) * B_magma.gen(i + 1)
        for i in range(3)
    )


def sage_F_ideal_to_magma(F_magma, x):
    Zm = F_magma.RingOfIntegers()
    gens = x.gens_two()
    return (
        sage_F_elt_to_magma(F_magma, gens[0]) * Zm
        + sage_F_elt_to_magma(F_magma, gens[1]) * Zm
    )


def magma_F_elt_to_sage(F_sage, x, magma):
    if F_sage != QQ:
        return F_sage(
            sage_eval(
                magma.eval("[%s[i] : i in [1..%s]]" % (x.name(), F_sage.degree()))
            )
        )
    else:
        return F_sage(sage_eval(magma.eval("%s" % x.name())))


def magma_quaternion_to_sage(B_sage, x, magma):
    xvec = x.Vector()
    return B_sage(
        [magma_F_elt_to_sage(B_sage.base_ring(), xvec[m + 1], magma) for m in range(4)]
    )


def magma_integral_quaternion_to_sage(B_sage, O_magma, F_magma, x, magma):
    F = B_sage.base_ring()
    xseq = x.ElementToSequence()
    basis = O_magma.Basis()
    return sum(
        magma_F_elt_to_sage(F, F_magma(xseq[i + 1]), magma)
        * magma_quaternion_to_sage(B_sage, basis[i + 1], magma)
        for i in range(4)
    )


def magma_F_ideal_to_sage(F_sage, x, magma):
    gens = x.TwoElement(nvals=2)
    if F_sage == QQ:
        return ZZ.ideal(magma_F_elt_to_sage(QQ, gens[0], magma)) + ZZ.ideal(
            magma_F_elt_to_sage(QQ, gens[1], magma)
        )
    else:
        return F_sage.ideal(
            [
                magma_F_elt_to_sage(F_sage, gens[0], magma),
                magma_F_elt_to_sage(F_sage, gens[1], magma),
            ]
        )


def quaternion_algebra_invariants_from_ramification(
    F, I, S=None, optimize_through_magma=True, magma=None
):
    r"""
    Creates a quaternion algebra over a number field which ramifies exactly at
    the specified places. The algorithm is inspired by the current MAGMA implementation
    by John Voight.

    .. WARNING::

       At the moment the algorithm requires F to be of narrow class number one. This
       is only needed when calling the routine weak_approximation, whose current
       implementation is done under this assumption.

    INPUT:

    - ``F`` - a number field
    - ``I`` - an ideal in F
    - ``S`` - (default: None) a list of real embeddings or real places of F

    OUTPUT:

    - a quaternion algebra of discriminant I and whose set of infinite
      ramified places is S

    EXAMPLES::

        sage: F.<r> = QuadraticField(5)
        sage: from darmonpoints.util import quaternion_algebra_invariants_from_ramification
        sage: quaternion_algebra_invariants_from_ramification(F,F.ideal(11),[]); # random #  optional - magma
        (22, -22*r - 31)
        sage: F.<r> = NumberField(x^2 - x - 24)
        sage: D = F.ideal(106*r + 469)
        sage: S = [F.real_places()[0]]
        sage: a, b = quaternion_algebra_invariants_from_ramification(F,D,S) #  optional - magma
        sage: B = QuaternionAlgebra(F,a,b) #  optional - magma
        sage: B.discriminant() == D #  optional - magma
        True
        sage: a, b = quaternion_algebra_invariants_from_ramification(F,r+1,[]) #  optional - magma
        sage: B = QuaternionAlgebra(F,a,b) #  optional - magma
        sage: B.discriminant() == F.ideal(r + 1) #  optional - magma
        True
        sage: a,b = B.invariants() #  optional - magma
        sage: all([v(a) > 0 or v(b) > 0 for v in F.real_places()]) #  optional - magma
        True

    The number of ramified places must be even:

        sage: F.<r> = NumberField(x^2 - x - 24)
        sage: a, b = quaternion_algebra_invariants_from_ramification(F,r+4,[]) #  optional - magma
        Traceback (most recent call last):
        ...
        ValueError: Number of ramified places must be even
    """
    if S is None:
        S = []
    I = F.ideal(I)
    P = I.factor()
    if (len(P) + len(S)) % 2 != 0:
        raise ValueError("Number of ramified places must be even")
    if any([ri > 1 for _, ri in P]):
        raise ValueError("All exponents in the discriminant factorization must be odd")

    if optimize_through_magma:
        if magma is None:
            from sage.interfaces.magma import magma
        if F.gen().minpoly().degree() == 1:
            Fm = magma.RationalsAsNumberField()
        else:
            Fm = magma.NumberField(F.gen().minpoly())
        if len(S) == len(F.real_places()):
            Bm = magma.QuaternionAlgebra(sage_F_ideal_to_magma(Fm, I), Fm.RealPlaces())
        else:
            v = Fm.RealPlaces()
            Bm = magma.QuaternionAlgebra(
                sage_F_ideal_to_magma(Fm, I), [v[i + 1] for i in S]
            )

        a, b = Bm.StandardForm(nvals=2)
        a = magma_F_elt_to_sage(F, a, magma)
        b = magma_F_elt_to_sage(F, b, magma)
        return a, b

    Foo = F.real_places(prec=Infinity)
    T = F.real_places(prec=Infinity)
    Sold, S = S, []
    for v in Sold:
        for w in T:
            if w(F.gen()) == v(F.gen()):
                S.append(w)
                T.remove(w)
                break
    if len(S) != len(Sold):
        raise ValueError("Please specify more precision for the places.")
    a = weak_approximation(F, I, J=None, S=S, T=[v for v in Foo if v not in S])
    if len(P) == 0 and all(
        [F.hilbert_symbol(-F.one(), a, pp) == 1 for pp, _ in F.ideal(2 * a).factor()]
    ):
        return -F.one(), a
    Ps = []
    for p, _ in P:
        if F.ideal(2).valuation(p) == 0:
            Ps.append((p, 1, False))
        else:
            Ps.append((p, 2 * p.ramification_index() + 1, False))
    if len(Ps) == 0:
        ps2 = F.ideal(a).factor()
    else:
        ps2 = prod([p**e for p, e, _ in Ps], F.ideal(1))
        ps2 = (F.ideal(a) / (F.ideal(a) + ps2)).factor()
    for p, _ in ps2:
        if F.ideal(2).valuation(p) == 0:
            Ps.append((p, 1, True))
        else:
            Ps.append((p, 2 * p.ramification_index() + 1, True))
    Ps.extend(
        [
            (p, 2 * p.ramification_index() + 1, True)
            for p, e in F.ideal(2).factor()
            if F.ideal(a).valuation(p) == 0
        ]
    )
    m = prod([p**e for p, e, _ in Ps], F.ideal(1))
    mnorm = m.norm().abs()
    passed = False
    while not passed:
        cnt = 0
        n = F.degree()
        bbnd = min(max(20, RR(m.norm().abs()).sqrt()), 10**4)  # Thanks, Steve!
        for _ in range(10):
            cnt += 1
            b = F.zero()
            while b == F.zero() or ZZ((F.ideal(b) + m).pari_hnf()[0, 0]) != 1:
                b = m.reduce(F.maximal_order().random_element(mnorm + 1))
            Sminus = []
            Splus = []
            for v in S:
                if v(b) > 0:
                    Sminus.append(v)
                else:
                    Splus.append(v)
            ub = weak_approximation(F, S=Sminus, T=Splus)
            b *= ub
            passed = True
            for p, e, condition in Ps:
                if e > 1 and (F.hilbert_symbol(a, b, p) == 1) != condition:
                    passed = False
                    break
                if (
                    e == 1
                    and (p.residue_symbol(b, ZZ(2), check=False) == 1) != condition
                ):
                    passed = False
                    break
            Fb = F.ideal(b)
            if passed and ZZ(Fb.pari_hnf()[0, 0]) != 1 and not Fb.is_prime():
                m1 = ZZ(m.pari_hnf()[0, 0])
                T = [v for v in Foo if v(b * m1) < 0]
                Tcomp = [v for v in Foo if v not in T]
                ubm1 = weak_approximation(F, S=T, T=Tcomp)
                Fb = F.ideal(b)
                while (
                    cnt <= bbnd and ZZ(Fb.pari_hnf()[0, 0]) != 1 and not Fb.is_prime()
                ):
                    b += ubm1 * m1
                    Fb = F.ideal(b)
                    cnt += 1
            if cnt > bbnd:
                cnt = 0
                m *= 2
                mnorm = m.norm().abs()
                passed = False
            if passed:
                if optimize_through_magma:
                    from sage.interfaces.magma import magma

                    if F.gen().minpoly().degree() == 1:
                        Fm = magma.RationalsAsNumberField()
                    else:
                        Fm = magma.NumberField(F.gen().minpoly())
                    Bm = magma.QuaternionAlgebra(
                        Fm, sage_F_elt_to_magma(Fm, a), sage_F_elt_to_magma(Fm, b)
                    ).OptimizedRepresentation()
                    a, b = Bm.StandardForm(nvals=2)
                    a = magma_F_elt_to_sage(F, a, magma)
                    b = magma_F_elt_to_sage(F, b, magma)
                assert all([v(a) < 0 or v(b) < 0 for v in S])
                return a, b


def weak_approximation(self, I=None, S=None, J=None, T=None):
    r"""

    Weak approximation at finite places if a number field


    .. WARNING::

       When S or T are non-empty, it is only implemented for number fields of
       narrow class number 1.

    INPUT:

    - ``I`` - a fractional ideal (trivial by default) of ``self``.
    - ``S`` - a list (empty by default) of real places of ``self``.
    - ``J`` - a fractional ideal (trivial by default) of ``self``.
    - ``T`` - a list (empty by default) of real places of ``self``.

    OUTPUT:

    An element x in ``self`` satisfying:
        1. `v_p(x) = v_p(I)` for all prime ideals `p` dividing ``I``.
        2. `v_p(x) = 0` for all prime ideals `p` dividing ``J``.
        3. `v_p(x) \geq 0` for all prime ideals coprime to ``I``+``J``.
        4. `v(x) < 0` for all places `v` in ``S``.
        5. `v(x) > 0` for all places `v` in ``T``.

    EXAMPLES::

        sage: from darmonpoints.util import weak_approximation
        sage: F.<r> = NumberField(x^2 - x - 24)
        sage: P3 = F.prime_above(3)
        sage: P11 = F.prime_above(11)
        sage: a = weak_approximation(F, P3^2 * P11^3); a
        196*r + 141
        sage: a.valuation(P3)
        2
        sage: a.valuation(P11)
        3
        sage: F.<r> = NumberField(x^4 - x -1)
        sage: P = F.prime_above(7)
        sage: Q = F.prime_above(13)
        sage: R = F.prime_above(23)
        sage: b = weak_approximation(F,P * Q * R); b
        -r^3 + 9*r^2 + 28*r - 19
        sage: b.valuation(P), b.valuation(Q), b.valuation(R)
        (1, 1, 1)
        sage: F.<r> = NumberField(x^4 - x - 12)
        sage: weak_approximation(F,S = [F.real_places()[0]], T =[F.real_places()[1]])
        11*r^3 - 43*r^2 - 32*r + 143
    """
    if S is None:
        S = []
    if T is None:
        T = []
    if (len(S) > 0 or len(T) > 0) and len(self.narrow_class_group()) > 1:
        raise NotImplementedError(
            "Only implemented for fields of narrow class number 1"
        )
    nf = self.pari_nf()
    n = 0
    entrylist = []
    if I is not None:
        for p, e in I.factor():
            entrylist.extend([p.pari_prime(), e])
            n += 1
    if J is not None:
        for p, _ in J.factor():
            entrylist.extend([p.pari_prime(), 0])
            n += 1
    if n > 0:
        a = self(nf.idealappr(pari.matrix(n, 2, entrylist), 1))
    else:
        a = self.one()
    if len(S) == 0 and len(T) == 0:
        return a
    else:
        Funits = list(self.units()) + [-1]
        Sa = [-v(a).sign() for v in S] + [v(a).sign() for v in T]
        ST = S + T
        for uu in product([False, True], repeat=len(Funits)):
            u = prod((eps for eps, i in zip(Funits, uu) if i), self.one())
            if all((v(u).sign() == e for v, e in zip(ST, Sa))):
                return a * u
    assert 0, "Signs not compatible"


def recognize_J(
    E,
    J,
    K,
    local_embedding=None,
    known_multiple=1,
    twopowlist=None,
    prec=None,
    outfile=None,
    qEpows=None,
):
    p = J.parent().prime()
    if prec is None:
        prec = J.precision_relative()
    QQp = Qp(p, prec)
    if local_embedding is None:
        local_embedding = QQp
    hK = K.class_number()
    Eloc = E.change_ring(local_embedding)
    # Tate parameter
    if qEpows is None:
        qE = tate_parameter(Eloc, QQp)
    else:
        qE = qEpows[1]

    valqE = QQ(qE.valuation())
    numqE, denqE = valqE.numerator(), valqE.denominator()

    ulog = 1 / numqE * (ZZ(p) ** numqE / qE**denqE).log()
    Jlog = J.log(p_branch=ulog)
    Cp = Jlog.parent()
    candidate = None
    if twopowlist is None:
        twopowlist = [QQ(2), QQ(1), QQ(1) / QQ(2)]
    HCF = K.hilbert_class_field(names="r1") if hK > 1 else K
    # Precalculate powers of qE
    precp = max((prec / valqE).floor() + 4, ((prec + 4) / valqE).floor() + 2)
    if qEpows is None:
        qEpows = [Cp(1)]
        for i in range(precp):
            qEpows.append(Cp(qE) * qEpows[-1])

    CEloc, _ = get_C_and_C2(Eloc, qEpows, Cp, precp)
    EH = E.change_ring(HCF)
    for twopow in twopowlist:
        success = False
        power = QQ(twopow * known_multiple) ** -1
        pnum = E.torsion_order() * power.numerator()
        pden = E.torsion_order() * power.denominator()
        J1list = sum(
            (
                our_nroot(J**pnum * qE**i, pden, return_all=True)
                for i in range(pden)
            ),
            [],
        )
        for J1 in J1list:
            if J1 == Cp(1):
                candidate = E.change_ring(HCF)(0)
                verbose("Recognized the point, it is zero!")
                success = True
                break
            else:
                pt = getcoords(Eloc, J1, prec, qEpows=qEpows, C=CEloc)
                try:
                    x, y = pt
                except TypeError:
                    assert pt is Infinity
                    candidate = E.change_ring(HCF)(0)
                    verbose("Recognized the point, it is zero!")
                    success = True
                    break
                if x.valuation() < -(prec - 2) and y.valuation() < -(prec - 2):
                    pt = Infinity
                    candidate = E.change_ring(HCF)(0)
                    verbose("Recognized the point, it is zero!")
                    success = True
                    break
                success = False
                prec0 = prec
                while not success and prec0 > 0.9 * prec:
                    verbose(
                        "Trying to recognize point with precision %s" % prec0, level=2
                    )
                    candidate, success = recognize_point(
                        x, y, E, K, prec=prec0, HCF=HCF, E_over_HCF=EH
                    )
                    prec0 -= 1

                if success:
                    verbose("Recognized the point!")
                    fwrite("x, y = %s,%s" % (x.add_bigoh(10), y.add_bigoh(10)), outfile)
                    break
        if success:
            assert known_multiple * twopow * J1.log(p_branch=ulog) == J.log(
                p_branch=ulog
            )
            return candidate, twopow, J1
    assert not success
    return None, None, None


def discover_equation(
    qE, emb, conductor, prec, field=None, check_conductor=True, height_threshold=0.85
):
    qElog = qE.log(p_branch=0) / qE.valuation()
    F = emb.domain() if field is None else field
    deg = F.degree()
    p = qElog.parent().prime()
    try:
        Ftors = F.unit_group().torsion_generator()
        Funits = [F(Ftors) ** i for i in range(Ftors.order())]
        for u in F.units():
            Funits = [u0 * u**i for u0, i in product(Funits, range(-6, 7))]
    except AttributeError:
        Funits = [-1, +1]
    try:
        primedivisors = [o[0].gens_reduced()[0] for o in conductor.factor()]
    except AttributeError:
        primedivisors = [o[0] for o in conductor.factor()]
    S = [o[0] for o in conductor.factor()]
    E4 = EisensteinForms(weight=4).basis()[0]
    Deltamodform = CuspForms(weight=12).basis()[0]
    jpowseries = E4.q_expansion(prec + 7) ** 3 / Deltamodform.q_expansion(prec + 7)
    jpowseries = PolynomialRing(ZZ, names="w")(
        [ZZ(jpowseries[i]) for i in range(prec + 1)]
    )
    Kp = emb.codomain()
    qElog = Kp(qElog.trace() / 2)
    w3s = [Kp(1)] + [o for o, _ in PolynomialRing(Kp, names="w")([1, 1, 1]).roots()]
    roots_of_unity = [Kp.teichmuller(a) for a in range(1, p)]
    qE0 = qElog.exp()
    for zeta, D in product(roots_of_unity, selmer_group_iterator(F, S, 12)):
        Deltap = Kp(emb(D))
        Deltapval = Deltap.valuation()
        qE = (p * qE0) ** Deltapval * zeta
        jE = 1 / qE + jpowseries(qE)
        c4cubed = Kp(Deltap * jE)
        try:
            c4root = our_cuberoot(c4cubed, Kp)
        except ValueError:
            continue
        for w3 in w3s:
            try:
                tmp = (c4root * w3).add_bigoh(prec)
                c4pol = our_algdep(tmp, deg)
            except ValueError:
                continue
            except TypeError:
                print(tmp)
                assert 0  # DEBUG
                continue
            if height_polynomial(c4pol, base=p) > height_threshold * prec:
                continue
            for c4ex, _ in c4pol.roots(F):
                c6squared = F(c4ex**3 - 1728 * D)
                if not c6squared.is_square():
                    continue
                for c6ex in c6squared.sqrt(all=True):
                    try:
                        E = EllipticCurve_from_c4c6(c4ex, c6ex)
                    except ArithmeticError:
                        continue
                    if not check_conductor or E.conductor() == conductor:
                        verbose("Success!")
                        return E
    verbose("Curve not recognized")
    return None


def covolume(F, D, M=1, prec=None, zeta=None):
    n = F.degree()
    if prec is None:
        prec = 53
    disc = ZZ(F.discriminant())
    if n > 1:
        if zeta is None:
            zetaf = F.zeta_function(prec)(2)
        else:
            zetaf = zeta
    else:
        if zeta is None:
            zetaf = Function_zeta()(RealField(prec)(2))
        else:
            zetaf = zeta

    if F != QQ:
        M = F.ideal(M)
        Phi = QQ(1)
        for P, _ in D.factor():
            Phi *= QQ(P.norm().abs() - 1)
        Psi = ZZ(1)
        for P, e in M.factor():
            np = QQ(P.norm())
            Psi *= np ** (ZZ(e) - 1) * (np + 1)
    else:
        M = ZZ(M)
        Phi = ZZ(D)
        for np, _ in D.factor():
            Phi *= QQ(1) - QQ(1) / np
        Psi = ZZ(1)
        for np, e in M.factor():
            Psi *= np ** (ZZ(e) - 1) * (np + 1)
    RR = RealField(prec)
    covol = (RR(disc).abs() ** (3.0 / 2.0) * zetaf * Phi) / (
        (4 * RR.pi() ** 2) ** (F.degree() - 1)
    )
    index = RR(Psi)
    indexunits = 1  # There is a factor missing here, due to units.
    return covol * index / indexunits


def simplification_isomorphism(G, return_inverse=False):
    """
    Return an isomorphism from ``self`` to a finitely presented group with
    a (hopefully) simpler presentation.

    EXAMPLES::

        sage: from sage.groups.free_group import FreeGroup
        sage: G.<a,b,c> = FreeGroup()
        sage: H = G / [a*b*c, a*b^2, c*b/c^2]
        sage: I = H.simplification_isomorphism()
        sage: I # random
        Generic morphism:
          From: Finitely presented group < a, b, c | a*b*c, a*b^2, c*b*c^-2 >
          To:   Finitely presented group < b |  >
        sage: I(a), I(b), I(c) # random
        b^-2, b, b

    TESTS::

        sage: from sage.groups.free_group import FreeGroup
        sage: F = FreeGroup(1)
        sage: G = F.quotient([F.0])
        sage: G.simplification_isomorphism() # random
        Generic morphism:
          From: Finitely presented group < x | x >
          To:   Finitely presented group <  |  >
          Defn: x |--> 1

    ALGORITM:

    Uses GAP.
    """
    I = G.gap().IsomorphismSimplifiedFpGroup()
    domain = G
    codomain = wrap_FpGroup(I.Range())
    phi = lambda x: codomain(I.ImageElm(x.gap()))
    ans = G.hom(phi, codomain)
    if return_inverse:
        Iinv = I.InverseGeneralMapping()
        phi_inv = lambda x: domain(Iinv.ImageElm(x.gap()))
        return ans, codomain.hom(phi_inv, G)
    else:
        return ans


def update_progress(progress, msg=""):
    barLength = 20  # Modify this to change the length of the progress bar
    if len(msg) > 0:
        msg = "( %s )" % msg
    if isinstance(progress, int):
        progress = float(progress)
    if not isinstance(progress, float):
        progress = 0
        status = "error: progress var must be float\r\n"
    if progress < 0:
        progress = 0
        status = "Halt...%s\r\n" % msg
    elif progress >= 1:
        progress = 1
        status = "Done...%s\r\n" % msg
    else:
        status = msg

    block = int(round(barLength * progress))
    text = "\rPercent: [{0}] {1:.2f}% {2}".format(
        "#" * block + "-" * (barLength - block), progress * 100, status
    )
    sys.stdout.write(text)
    sys.stdout.flush()


def selmer_group_iterator(self, S, m, proof=True):
    r"""
    Return an iterator through elements of the finite group `K(S,m)`.
    [1, -1, 13, -13, 11, -11, 143, -143]
    """
    if self == QQ:
        KSgens = [o for o in S] + [QQ(-1)]
    else:
        KSgens = self.selmer_generators(S=S, m=m, proof=proof)
    f = lambda o: m if o is Infinity else o.gcd(m)
    orders = [f(a.multiplicative_order()) for a in KSgens]
    one = self.one()
    for ev in cartesian_product_iterator(
        [range(-o // 2, (1 + o) // 2) for o in orders]
    ):
        yield prod([p**e for p, e in zip(KSgens, ev)], one)


def print_table_latex(self, header_string=None):
    r"""
    LaTeX representation of a table.

    If an entry is a Sage object, it is replaced by its LaTeX
    representation, delimited by dollar signs (i.e., ``x`` is
    replaced by ``$latex(x)$``). If an entry is a string, the
    dollar signs are not automatically added, so tables can
    include both plain text and mathematics.

    EXAMPLES::

        sage: from sage.misc.table import table
        sage: a = [[r'$\sin(x)$', '$x$', 'text'], [1,34342,3], [identity_matrix(2),5,6]]
        sage: latex(table(a)) # indirect doctest
        \begin{tabular}{lll}
        $\sin(x)$ & $x$ & text \\
        $1$ & $34342$ & $3$ \\
        $\left(\begin{array}{rr}
        1 & 0 \\
        0 & 1
        \end{array}\right)$ & $5$ & $6$ \\
        \end{tabular}
        sage: latex(table(a, frame=True, align='center'))
        \begin{tabular}{|c|c|c|} \hline
        $\sin(x)$ & $x$ & text \\ \hline
        $1$ & $34342$ & $3$ \\ \hline
        $\left(\begin{array}{rr}
        1 & 0 \\
        0 & 1
        \end{array}\right)$ & $5$ & $6$ \\ \hline
        \end{tabular}
    """
    rows = self._rows
    nc = len(rows[0])
    if len(rows) == 0 or nc == 0:
        return ""

    align_char = self._options["align"][0]  # 'l', 'c', 'r'
    if self._options["frame"]:
        frame_char = "|"
        frame_str = " \\hline"
    else:
        frame_char = ""
        frame_str = ""
    if self._options["header_column"]:
        head_col_char = "|"
    else:
        head_col_char = ""
    if self._options["header_row"]:
        head_row_str = " \\hline"
    else:
        head_row_str = ""

    # table header
    s = "\\begin{tabular}{"
    if header_string is None:
        s += frame_char + align_char + frame_char + head_col_char
        s += frame_char.join([align_char] * (nc - 1))
        s += frame_char
    else:
        s += header_string
    s += "}" + frame_str + "\n"
    # first row
    s += " & ".join(
        LatexExpr(x)
        if isinstance(x, (str, LatexExpr))
        else "$" + latex(x).strip() + "$"
        for x in rows[0]
    )
    s += " \\\\" + frame_str + head_row_str + "\n"
    # other rows
    for row in rows[1:]:
        s += " & ".join(
            LatexExpr(x)
            if isinstance(x, (str, LatexExpr))
            else "$" + latex(x).strip() + "$"
            for x in row
        )
        s += " \\\\" + frame_str + "\n"
    s += "\\end{tabular}"
    return s


class Bunch:
    def __init__(self, **kwds):
        self.__dict__.update(kwds)

    def update(self, **v):
        self.__dict__.update(**v)

    def get(self, name, default=None):
        try:
            return self.__dict__[name]
        except KeyError:
            return default


def config_section_map(config, section):
    dict1 = {}
    try:
        options = config.options(section)
    except configparser.NoSectionError:
        return dict1
    for option in options:
        try:
            dict1[option] = sage_eval(config.get(section, option))
        except NameError:
            print("exception on %s!" % option)
            dict1[option] = None
        except configparser.NoSectionError:
            dict1[option] = None
    return dict1


def print_padic(x):
    R = x.parent()
    with local_print_mode(R, "val-unit"):
        print(x)


def relativize_ATR(F, ff):
    return [pp.discriminant() for pp, _ in ff.change_ring(F).factor()]


def field_element_pari_to_sage(w, Fp, elt):
    gp = Fp.parent()
    yp = gp.variable(Fp)
    return sage_eval(str(elt), locals={"y": w})


def pari_ordmax_basis_to_sage(w, Ap):
    gp = Ap.parent()
    Fp = Ap.algcenter()
    stdbasis = [
        gp.mattranspose(list(e)) for e in (ZZ ** (4 * Fp[1].poldegree())).basis()
    ]
    c = lambda o: field_element_pari_to_sage(w, Fp, o)
    Omaxbasis = [[c(o) for o in gp.algbasisto1ijk(Ap, e)] for e in stdbasis]
    return Omaxbasis


def sage_order_basis_to_pari(w, Ap, basis):
    gp = Ap.parent()
    paribasis = []
    wcoords = w.coordinates_in_terms_of_powers()
    for b in basis:
        coefs = b.coefficient_tuple()
        bp = gp.alg1ijktobasis(Ap, [QQ["y"](wcoords(o)) for o in coefs])
        paribasis.append(bp)
    return gp.matconcat(paribasis)
