r"""
Fundamental domains and presentations of arithmetic Kleinian groups.

This is a Python port of Aurel Page's Magma package *KleinianGroups 1.0*
(see ``darmonpoints/KleinianGroups-1.0``; GPL-3), restricted to what
darmonpoints needs: the ``NormalizedBasis`` algorithm with the
"SmallBalls" enumeration and the "Reduction" pairing method, for the norm one
group or the unit group of an order, and the ``Presentation`` routine.

Reference: A. Page, *Computing arithmetic Kleinian groups*, Math. Comp. 84
(2015).

Points of hyperbolic 3-space are in the unit ball model, represented (as in
Page's code) by Hamilton quaternions ``x0 + x1*i + x2*j`` (the ``k``
coordinate is zero). Real numbers are ``gmpy2.mpfr`` with a working precision
given in decimal digits, and quaternions are 4-tuples of them.

The arithmetic input is described by :class:`KleinianOrderData`, which only
needs the quaternion algebra ``B`` over a number field with exactly one
complex place (``B`` ramified at all the real places), a `\ZZ`-basis of the
order and a membership test.

EXAMPLES:

The maximal order of the quaternion algebra over `\QQ(\sqrt{-7})` ramified
at the two primes above `2`::

    sage: from darmonpoints.kleinian import *
    sage: from darmonpoints.quatorder import QuaternionAlgebraPari
    sage: from darmonpoints.util import quaternion_algebra_invariants_from_ramification
    sage: F.<w> = NumberField(x^2 - x + 2)
    sage: P, Q = [P for P, _ in F.ideal(2).factor()]
    sage: a, b = quaternion_algebra_invariants_from_ramification(F, P * Q, [])
    sage: QA = QuaternionAlgebraPari(F, a, b)
    sage: M = QA.maximal_order_matrix()
    sage: data = KleinianOrderData(QA.B, QA.order_basis(M), lambda x: QA.is_in_order(M, x))
    sage: res = normalized_basis(data, pr=40, seed=1)
    sage: abs(res['volume'] / res['covolume'] - 1) < 10^-10
    True
    sage: gens, rels = presentation(res['faces'], res['finite_edges'], data, res['ctx'], res['embedding'])
    sage: words = [prod(gens[abs(i) - 1]**sign(i) for i in r) for r in rels]
    sage: all(g == g.conjugate() for g in words)  # relations hold up to the centre
    True
    sage: new_rels, images, preimages = simplify_presentation(len(gens), rels)
    sage: len(preimages) <= len(gens)
    True
"""

import random as _pyrandom
from math import floor
from math import log as _flog

import gmpy2
from gmpy2 import mpc, mpfr
from sage.misc.prandom import randint as _sage_randint
from sage.misc.verbose import verbose
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ


class KleinianTimeout(RuntimeError):
    pass


# ---------------------------------------------------------------------------
# Real numbers and quaternions
# ---------------------------------------------------------------------------


class _Ctx:
    r"""
    Working precision (in decimal digits) and the derived epsilons.
    """

    def __init__(self, pr):
        self.pr = pr
        self.bits = int(pr * 3.3219280948873626) + 10
        gmpy2.get_context().precision = self.bits
        self.pi = gmpy2.const_pi()
        self.pi2 = 2 * self.pi
        self.zero = mpfr(0)
        self.one = mpfr(1)
        self.eps12 = self.epsilon(QQ(1) / 2)
        self.eps13 = self.epsilon(QQ(1) / 3)
        self.eps110 = self.epsilon(QQ(1) / 10)
        self.eps910 = self.epsilon(QQ(9) / 10)

    def epsilon(self, r):
        return mpfr(10) ** (-mpfr(float(r)) * self.pr)

    def R(self, x):
        r"""
        Convert a Sage real/rational number to mpfr.
        """
        if x in QQ:
            x = QQ(x)
            return mpfr(int(x.numerator())) / int(x.denominator())
        try:
            return mpfr(x)
        except TypeError:
            return mpfr(str(x))


def qadd(x, y):
    return (x[0] + y[0], x[1] + y[1], x[2] + y[2], x[3] + y[3])


def qsub(x, y):
    return (x[0] - y[0], x[1] - y[1], x[2] - y[2], x[3] - y[3])


def qscal(c, x):
    return (c * x[0], c * x[1], c * x[2], c * x[3])


def qmul(x, y):
    a1, b1, c1, d1 = x
    a2, b2, c2, d2 = y
    return (
        a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2,
        a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2,
        a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2,
        a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2,
    )


def qconj(x):
    return (x[0], -x[1], -x[2], -x[3])


def sqrnorm(x):
    return x[0] * x[0] + x[1] * x[1] + x[2] * x[2] + x[3] * x[3]


def qinv(x):
    n = sqrnorm(x)
    return (x[0] / n, -x[1] / n, -x[2] / n, -x[3] / n)


def qzero():
    z = mpfr(0)
    return (z, z, z, z)


def qreal(r):
    z = mpfr(0)
    return (mpfr(r), z, z, z)


def point(x):
    return (x[0], x[1], x[2], mpfr(0))


def vecprod(x, y):
    return (
        x[1] * y[2] - x[2] * y[1],
        x[2] * y[0] - x[0] * y[2],
        x[0] * y[1] - x[1] * y[0],
        mpfr(0),
    )


def colinear(x, y, eps):
    return (
        abs(x[1] * y[2] - x[2] * y[1]) <= eps
        and abs(x[2] * y[0] - x[0] * y[2]) <= eps
        and abs(x[0] * y[1] - x[1] * y[0]) <= eps
    )


def triple(x, y, z):
    return (
        (x[1] * y[2] - x[2] * y[1]) * z[0]
        + (x[2] * y[0] - x[0] * y[2]) * z[1]
        + (x[0] * y[1] - x[1] * y[0]) * z[2]
    )


def scalar(x, y):
    return x[0] * y[0] + x[1] * y[1] + x[2] * y[2]


# 2x2 matrices over the quaternions: tuples (A, B, C, D)


def mmul(m, n):
    A, B, C, D = m
    E, F, G, H = n
    return (
        qadd(qmul(A, E), qmul(B, G)),
        qadd(qmul(A, F), qmul(B, H)),
        qadd(qmul(C, E), qmul(D, G)),
        qadd(qmul(C, F), qmul(D, H)),
    )


def action(ctx, g, w):
    r"""
    Action of ``g`` on the point ``w`` of the unit ball.
    """
    A, B, C, D = g
    gw = qmul(qadd(qmul(A, w), B), qinv(qadd(qmul(C, w), D)))
    gw = point(gw)
    n = sqrnorm(gw)
    if n >= 1:
        gw = qscal((1 - ctx.eps910) / gmpy2.sqrt(n), gw)
    return gw


def zero_to_p(ctx, p):
    r"""
    Matrices sending 0 to ``p`` and back (Page's ``ZerotoP``).
    """
    r2 = 1 - sqrnorm(p)
    if r2 <= 0:
        return zero_to_p(ctx, qscal(1 - ctx.eps910, p))
    ri = 1 / gmpy2.sqrt(r2)
    one = qreal(ri)
    mone = qreal(-ri)
    pp = qscal(ri, p)
    pc = qscal(ri, qconj(p))
    return (one, qscal(-1, pp), pc, mone), (mone, pp, qscal(-1, pc), one)


# ---------------------------------------------------------------------------
# Spheres, circles and intervals
# ---------------------------------------------------------------------------


class Sphere:
    __slots__ = ("center", "radius", "g", "matrix", "edges")

    def __init__(self, center, radius, g=None, matrix=None):
        self.center = center
        self.radius = radius
        self.g = g
        self.matrix = matrix
        self.edges = set()


class Circle:
    __slots__ = ("center", "radius", "e1", "e2", "e3")

    def __init__(self, center, radius, orthogonal=None):
        self.center = center
        self.radius = radius
        if orthogonal is not None:
            self.e3 = orthogonal
            self.e1, self.e2 = plane_basis(orthogonal)


def plane_basis(N):
    i = (mpfr(0), mpfr(1), mpfr(0), mpfr(0))
    e1 = point(qmul(i, N))
    if sqrnorm(e1) == 0:
        e1 = qadd(e1, qreal(1))
    else:
        e1 = qscal(1 / gmpy2.sqrt(sqrnorm(e1)), e1)
    e2 = vecprod(N, e1)
    e2 = qscal(1 / gmpy2.sqrt(sqrnorm(e2)), e2)
    return e1, e2


def angle_in_plane(ctx, x, e1, e2):
    z = mpc(scalar(x, e1), scalar(x, e2))
    if z == 0:
        return mpfr(0)
    theta = gmpy2.phase(z)
    if theta < 0:
        theta += ctx.pi2
    return theta


def point_in_circle(C, theta):
    return qadd(
        C.center,
        qscal(
            C.radius, qadd(qscal(gmpy2.cos(theta), C.e1), qscal(gmpy2.sin(theta), C.e2))
        ),
    )


def delta_dist(u, v):
    return sqrnorm(qsub(u, v)) / ((1 - sqrnorm(u)) * (1 - sqrnorm(v)))


def is_interior(w, S, eps):
    return sqrnorm(qsub(w, S.center)) <= S.radius**2 * (1 + eps)


def is_exterior(w, S, eps):
    return sqrnorm(qsub(w, S.center)) >= S.radius**2 * (1 - eps)


def intersection_angle(S1, S2):
    cosa = (sqrnorm(qsub(S1.center, S2.center)) - (S1.radius**2 + S2.radius**2)) / (
        2 * S1.radius * S2.radius
    )
    if abs(cosa) > 1:
        raise ValueError("The spheres do not intersect.")
    return gmpy2.acos(cosa)


def _isscalar(x):
    return x == x.conjugate()


def _key(x):
    r"""
    A hashable key for a quaternion. We use the rational coordinates since
    ``coefficient_tuple()`` over number fields may contain non-normalized
    zeros (a Sage bug) that hash and compare inconsistently.
    """
    return tuple(tuple(c.list()) for c in x.coefficient_tuple())


def spheres_intersection(ctx, S1, S2):
    N = qsub(S2.center, S1.center)
    D = sqrnorm(N)
    if D <= ctx.eps12:
        return Circle(None, mpfr(-1))
    M = qscal(mpfr(1) / 2, qadd(S2.center, S1.center))
    R1 = S1.radius
    R2 = S2.radius
    Rsqr = ((R1 + R2) ** 2 - D) * (D - (R1 - R2) ** 2) / (4 * D)
    if Rsqr < 0:
        return Circle(None, mpfr(-1))
    if Rsqr < ctx.eps12 and S1.g is not None and S2.g is not None:
        g1, g2 = S1.g, S2.g
        if (
            g1.reduced_trace() ** 2 == 4
            and g2.reduced_trace() ** 2 == 4
            and _isscalar(g1 * g2 * (g2 * g1) ** -1)
        ):
            return Circle(None, mpfr(-1))
    return Circle(qadd(M, qscal((R1**2 - R2**2) / (2 * D), N)), gmpy2.sqrt(Rsqr), N)


def points_to_sphere(x, y, z):
    a = y[0] - x[0]
    b = y[1] - x[1]
    c = z[0] - x[0]
    d = z[1] - x[1]
    alpha = (sqrnorm(y) - sqrnorm(x)) / 2
    beta = (sqrnorm(z) - sqrnorm(x)) / 2
    D = a * d - b * c
    if D == 0:
        return Sphere(x, mpfr(0))
    t1 = (d * alpha - b * beta) / D
    t2 = (a * beta - c * alpha) / D
    Y = (t1, t2, mpfr(0), mpfr(0))
    return Sphere(Y, gmpy2.sqrt(sqrnorm(qsub(Y, x))))


def end_points(e):
    C, I = e[0], e[1]
    p1 = point_in_circle(C, I[1])
    p2 = point_in_circle(C, I[2 % len(I)])
    if p1 == p2:
        return [p1]
    return [p1, p2]


def btoh(w):
    j = (mpfr(0), mpfr(0), mpfr(1), mpfr(0))
    return qmul(qinv(qadd(qreal(1), qmul(w, j))), qadd(w, j))


def perturbated_btoh(w):
    j = (mpfr(0), mpfr(0), mpfr(1), mpfr(0))
    if w == j:
        return qreal(mpfr(1000000000) / 1174263548)
    z = btoh(w)
    den = qadd(qscal(mpfr(1174263548) / 1000000000, z), qreal(1))
    return qmul(z, qinv(den))


def same_sphere(S1, S2, eps):
    return (
        sqrnorm(qsub(S1.center, S2.center)) < eps**2
        and abs(S1.radius - S2.radius) < eps
    )


def same_circle(C1, C2, eps):
    return (
        sqrnorm(qsub(C1.center, C2.center)) < eps**2
        and abs(C1.radius - C2.radius) < eps
        and sqrnorm(vecprod(C1.e3, C2.e3)) * C1.radius * C2.radius
        < sqrnorm(C1.e3) * sqrnorm(C2.e3) * eps**2
    )


def merge_intervals(L, threshold):
    n = len(L) // 2
    L2 = [(L[2 * i], 1) for i in range(n)] + [(L[2 * i + 1], -1) for i in range(n)]
    L2.sort()
    L3 = []
    count = 0
    flag = False
    for v, s in L2:
        count += s
        if (count >= threshold) != flag:
            flag = not flag
            L3.append(v)
    return L3


def intersection_compacts(Li, B):
    k = len(Li)
    if k == 0:
        return [mpfr(0), B]
    return merge_intervals([x for I in Li for x in I], k)


def length_interval(L):
    s = mpfr(0)
    for i in range(0, len(L) - 1, 2):
        s += L[i + 1] - L[i]
    return s


def point_in_interval(ctx, L):
    n = len(L)
    if L[0] == 0 and L[n - 1] == ctx.pi2:
        theta = (L[n - 2] + L[1] + ctx.pi2) / 2
        if theta >= ctx.pi2:
            theta -= ctx.pi2
        return theta
    return (L[0] + L[1]) / 2


# ---------------------------------------------------------------------------
# Exterior domains
# ---------------------------------------------------------------------------


def is_in_exterior_domain(w, L, eps):
    for s in L:
        if sqrnorm(qsub(w, s.center)) < s.radius**2 * (1 - eps):
            return False
    return True


def cut_interval(ctx, C, S, interior):
    r"""
    The union of intervals of angles of the points of the circle ``C`` that
    are in the interior (or exterior) of the sphere ``S``.
    """
    eps12 = ctx.eps12
    CCenter, Ce1, Ce2, Ce3 = C.center, C.e1, C.e2, C.e3
    SCenter = S.center
    R1 = S.radius
    R2 = C.radius
    pi2 = ctx.pi2
    if R2 >= eps12:
        N = qsub(CCenter, SCenter)
        D = sqrnorm(N)
        if D >= (R1 + R2) ** 2:
            return [] if interior else [mpfr(0), pi2]
        if R2 == 0:
            Inter = [CCenter] if D == R1**2 else []
        elif D <= eps12:
            if abs(R1 - R2) <= eps12:
                p0 = point_in_circle(C, mpfr(0))
                Inter = [p0, p0, p0]
            else:
                Inter = []
        else:
            M = qscal(mpfr(1) / 2, qadd(CCenter, SCenter))
            Cent = qadd(M, qscal((R1**2 - R2**2) / (2 * D), N))
            if not colinear(N, Ce3, eps12):
                Y = vecprod(Ce3, N)
                a = triple(Y, N, Ce3)
                Z = vecprod(Y, N)
                b = scalar(Ce3, qsub(CCenter, Cent))
                Pt = qadd(Cent, qscal(b / a, Z))
                A = sqrnorm(Y)
                Bc = scalar(Y, qsub(Pt, SCenter))
                CC = sqrnorm(qsub(Pt, SCenter)) - R1**2
                Delta = Bc**2 - 4 * A * CC
                if Delta < 0:
                    Inter = []
                elif Delta / A > eps12 * R2:
                    SD = gmpy2.sqrt(Delta)
                    Inter = [
                        qadd(Pt, qscal((-Bc + SD) / (2 * A), Y)),
                        qsub(Pt, qscal((Bc + SD) / (2 * A), Y)),
                    ]
                else:
                    Inter = [qsub(Pt, qscal(Bc / (2 * A), Y))]
            else:
                if abs(R1**2 - R2**2 - D) <= eps12:
                    p0 = point_in_circle(C, mpfr(0))
                    Inter = [p0, p0, p0]
                else:
                    Inter = []
        angles = [angle_in_plane(ctx, qsub(x, CCenter), Ce1, Ce2) for x in Inter]
    else:
        angles = []
    n = len(angles)
    if n > 2:
        return [mpfr(0), pi2]
    if n <= 1:
        ptci = qadd(
            CCenter, qscal(R2, qadd(qscal(mpfr(3) / 5, Ce1), qscal(mpfr(4) / 5, Ce2)))
        )
        ok = is_interior(ptci, S, eps12) if interior else is_exterior(ptci, S, eps12)
        return [mpfr(0), pi2] if ok else []
    a1, a2 = angles
    if a1 >= a2:
        a1, a2 = a2, a1
    theta = point_in_interval(ctx, [a1, a2])
    p = point_in_circle(C, theta)
    ok = is_interior(p, S, eps12) if interior else is_exterior(p, S, eps12)
    if ok:
        return [a1, a2]
    return [mpfr(0), a1, a2, pi2]


def interval_of_circle(ctx, C, L, usphere, skip):
    r"""
    Angles of the points of ``C`` exterior to the spheres of ``L`` (except
    the indices in ``skip``) and, if ``usphere``, interior to the unit sphere.
    """
    pi2 = ctx.pi2
    Linterv = []
    if usphere:
        Linterv.append(cut_interval(ctx, C, Sphere(qzero(), mpfr(1)), True))
    for s, S in enumerate(L):
        if s in skip:
            continue
        Linterv.append(cut_interval(ctx, C, S, False))
        if s % 20 == 19:
            if intersection_compacts(Linterv, pi2) == []:
                return []
    return intersection_compacts(Linterv, pi2)


def _eat_edges(ctx, E, S, FP):
    pi2 = ctx.pi2
    keep = []
    for e in E:
        interv = cut_interval(ctx, e[0], S, False)
        lg = length_interval(e[1])
        e[1] = intersection_compacts([e[1], interv], pi2)
        newlg = length_interval(e[1])
        if newlg < lg:
            FP |= e[2]
        if newlg > ctx.eps13:
            keep.append(e)
    E[:] = keep


def _new_edges(ctx, F, S, FP):
    unit = Sphere(qzero(), mpfr(1))
    NFE = []
    n = len(F)
    for f in sorted(FP):
        C = spheres_intersection(ctx, F[f], S)
        if C.radius >= ctx.eps13:
            interv = interval_of_circle(ctx, C, F, True, {f})
            if length_interval(interv) >= ctx.eps13:
                NFE.append([C, interv, {f, n}])
    C = spheres_intersection(ctx, unit, S)
    NIE = []
    if C.radius >= ctx.eps13:
        interv = interval_of_circle(ctx, C, F, False, set())
        if length_interval(interv) >= ctx.eps13:
            NIE = [[C, interv, {n}]]
    return NFE, NIE


def _eliminate_multiple_edges(ctx, F, E, NE, nbF):
    n = len(E)
    for ne in NE:
        old = False
        for edge in range(n):
            if same_circle(ne[0], E[edge][0], ctx.eps12):
                E[edge][2] = E[edge][2] | ne[2]
                old = True
                break
        if not old:
            E.append(ne)
    for e in E:
        if len(e[2]) > nbF:
            theta = point_in_interval(ctx, e[1])
            x = point_in_circle(e[0], theta)
            STest = Sphere(x, ctx.eps110)
            cands = []
            for f in sorted(e[2]):
                CTest = spheres_intersection(ctx, F[f], STest)
                lt = length_interval(interval_of_circle(ctx, CTest, F, True, {f}))
                cands.append((lt, f))
            cands.sort(key=lambda t: -t[0])
            e[2] = set(f for _, f in cands[:nbF])


def _eliminate_faces(F, FE, IE):
    setF = set()
    for e in FE:
        setF |= e[2]
    for e in IE:
        setF |= e[2]
    newF = sorted(setF)
    index = {f: i for i, f in enumerate(newF)}
    F[:] = [F[f] for f in newF]
    for f in F:
        f.edges = set()
    for ie, e in enumerate(FE):
        e[2] = set(index[f] for f in e[2])
        for f in e[2]:
            F[f].edges.add(ie)
    for e in IE:
        e[2] = set(index[f] for f in e[2])


def update_exterior_domain(ctx, F, FE, IE, S):
    r"""
    Intersect the polyhedron (faces ``F``, finite edges ``FE``, infinite
    edges ``IE``) with the exterior of the sphere ``S``. Modifies the lists.
    """
    for f in F:
        if same_sphere(f, S, ctx.eps12):
            return
    FP = set()
    _eat_edges(ctx, IE, S, FP)
    _eat_edges(ctx, FE, S, FP)
    NFE, NIE = _new_edges(ctx, F, S, FP)
    F.append(S)
    _eliminate_multiple_edges(ctx, F, FE, NFE, 2)
    _eliminate_multiple_edges(ctx, F, IE, NIE, 1)
    _eliminate_faces(F, FE, IE)


def exterior_domain(ctx, L):
    F, FE, IE = [], [], []
    for S in L:
        update_exterior_domain(ctx, F, FE, IE, S)
    return F, FE, IE


# ---------------------------------------------------------------------------
# Volumes
# ---------------------------------------------------------------------------


def compute_zetas(pr):
    N = floor(pr / _flog(4, 10)) + 1
    return [gmpy2.zeta(mpfr(2 * n)) / (n * (2 * n + 1)) for n in range(1, N + 1)]


def lobachevsky(ctx, x, zetas):
    pi = ctx.pi
    if x < 0:
        return -lobachevsky(ctx, -x, zetas)
    if x >= pi:
        return lobachevsky(ctx, x - gmpy2.floor(x / pi) * pi, zetas)
    if x > pi / 2:
        return -lobachevsky(ctx, pi - x, zetas)
    if x == 0:
        return mpfr(0)
    quo = x / pi
    quo2 = quo * quo
    logquo = gmpy2.log10(1 / quo2)
    N = int(
        gmpy2.floor(
            (ctx.pr + gmpy2.log10(mpfr(2) / 3) - gmpy2.log10(1 - quo2)) / logquo
        )
    )
    N = min(max(N, 0), len(zetas))
    value = mpfr(0)
    for n in range(N, 0, -1):
        value += zetas[n - 1]
        value *= quo2
    value *= x
    value += x - x * gmpy2.log(2 * x)
    return value


def _sign(x):
    return (x > 0) - (x < 0)


def _std_tetra(ctx, y, z, zetas):
    dist = abs(y - z)
    eps12 = ctx.eps12
    if abs(z) <= eps12 or dist <= eps12:
        return mpfr(0)
    cosalpha = abs(y) / abs(z)
    cosgamma = abs(y)
    alpha = mpfr(0) if cosalpha >= 1 else gmpy2.acos(cosalpha)
    gamma = gmpy2.acos(cosgamma)
    hpi = ctx.pi / 2
    return (
        lobachevsky(ctx, alpha + gamma, zetas)
        + lobachevsky(ctx, alpha - gamma, zetas)
        + 2 * lobachevsky(ctx, hpi - alpha, zetas)
    ) / 4


def _norm_c(z):
    return z.real**2 + z.imag**2


def _centered_tetra(ctx, y, z, zetas):
    N = _norm_c(z - y)
    if N < ctx.eps12:
        return mpfr(0)
    t = -(y * (z - y).conjugate()).real / N
    D = y + t * (z - y)
    return abs(
        _sign((D * z.conjugate()).imag) * _std_tetra(ctx, D, z, zetas)
        + _sign((y * D.conjugate()).imag) * _std_tetra(ctx, D, y, zetas)
    )


def _normalized_tetra(ctx, x, y, z, zetas):
    return abs(
        _sign((y * z.conjugate()).imag) * _centered_tetra(ctx, y, z, zetas)
        + _sign((x * y.conjugate()).imag) * _centered_tetra(ctx, x, y, zetas)
        + _sign((z * x.conjugate()).imag) * _centered_tetra(ctx, x, z, zetas)
    )


def _infinity_vertex_tetra(ctx, x, y, z, zetas):
    s = points_to_sphere(x, y, z)
    if s.radius == 0:
        return mpfr(0)
    X = qscal(1 / s.radius, qsub(x, s.center))
    Y = qscal(1 / s.radius, qsub(y, s.center))
    Z = qscal(1 / s.radius, qsub(z, s.center))
    return _normalized_tetra(
        ctx, mpc(X[0], X[1]), mpc(Y[0], Y[1]), mpc(Z[0], Z[1]), zetas
    )


def _semi_ideal_tetra(ctx, X, Y, Z, v, zetas):
    e = ctx.eps12
    if sqrnorm(qsub(X, v)) <= e or sqrnorm(qsub(Y, v)) <= e or sqrnorm(qsub(Z, v)) <= e:
        return mpfr(0)
    return _infinity_vertex_tetra(
        ctx, qinv(qsub(v, X)), qinv(qsub(v, Y)), qinv(qsub(v, Z)), zetas
    )


def _infinity_end(X, Y):
    x = (X[0], X[1], mpfr(0), mpfr(0))
    y = (Y[0], Y[1], mpfr(0), mpfr(0))
    d = sqrnorm(qsub(x, y))
    alpha = (sqrnorm(X) - sqrnorm(Y) + 2 * (sqrnorm(y) - scalar(x, y))) / d
    beta = (sqrnorm(Y) - sqrnorm(X) + 2 * (sqrnorm(x) - scalar(x, y))) / d
    S = qadd(qscal(alpha, x), qscal(beta, y))
    P = scalar(S, qscal(mpfr(1) / 2, qadd(x, y))) - (sqrnorm(X) + sqrnorm(Y)) / 2
    delta = sqrnorm(S) / 4 - P
    r = gmpy2.sqrt(delta)
    u = qscal(1 / gmpy2.sqrt(sqrnorm(qsub(y, x))), qsub(y, x))
    return qadd(qscal(mpfr(1) / 2, S), qscal(r, u))


def _tetrahedron_volume(ctx, X, Y, Z, V, zetas):
    e = ctx.eps12
    pts = [X, Y, Z, V]
    for i in range(4):
        for j in range(i + 1, 4):
            if sqrnorm(qsub(pts[i], pts[j])) <= e:
                return mpfr(0)
    v = _infinity_end(X, V)
    return _semi_ideal_tetra(ctx, X, Y, Z, v, zetas) - _semi_ideal_tetra(
        ctx, V, Y, Z, v, zetas
    )


def polyhedron_volume(ctx, F, E, zetas):
    edges_of_face = [[] for _ in F]
    for e in E:
        for f in e[2]:
            edges_of_face[f].append(end_points(e))
    tetras = []
    for f in range(len(F)):
        if not edges_of_face[f]:
            return None  # infinite volume
        x0 = edges_of_face[f][0][0]
        for ep in edges_of_face[f]:
            if len(ep) < 2:
                continue
            tetras.append([perturbated_btoh(x0)] + [perturbated_btoh(w) for w in ep])
    x00 = perturbated_btoh(edges_of_face[0][0][0])
    vol = mpfr(0)
    for t in tetras:
        vol += _tetrahedron_volume(ctx, t[0], t[1], t[2], x00, zetas)
    return vol


def volume_ball(r):
    return gmpy2.const_pi() * (gmpy2.sinh(2 * r) - 2 * r)


def d_volume_ball(r):
    return 2 * gmpy2.const_pi() * (gmpy2.cosh(2 * r) - 1)


def radius_ball(v, eps):
    if v <= eps:
        return (3 * v / (4 * gmpy2.const_pi())) ** (mpfr(1) / 3)
    r = max(gmpy2.log(2 * v / gmpy2.const_pi()) / 2, mpfr(1) / 10)
    while True:
        diffe = volume_ball(r) - v
        r = r - diffe / d_volume_ball(r)
        if abs(diffe) < v * eps:
            return r


# ---------------------------------------------------------------------------
# The arithmetic data
# ---------------------------------------------------------------------------


class KleinianOrderData:
    r"""
    An order in a quaternion algebra over a number field with exactly one
    complex place, ramified at all the real places.

    INPUT:

    - ``B`` -- the quaternion algebra (``B.invariants() == (a, b)``)
    - ``basis`` -- a `\ZZ`-basis of the order (elements of ``B``)
    - ``contains`` -- a function testing membership in the order
    - ``maximal`` -- optional :class:`KleinianOrderData` of a maximal order
      containing this one (needed when the order is not maximal)
    - ``center`` -- the point of upper half space (``[x, y, t]``) used to
      conjugate (default as in Page's code)
    - ``vC`` -- the complex place (default: the one with positive imaginary
      part on the generator of ``F``)
    """

    def __init__(
        self, B, basis, contains, maximal=None, center=None, vC=None, discriminant=None
    ):
        self.B = B
        self.F = B.base_ring()
        self.basis = list(basis)
        self.contains = contains
        self.maximal = maximal
        if center is None:
            center = [QQ(1) / 3, QQ(-1) / 2, QQ(17) / 5]
        self.center = [QQ(c) for c in center[:3]]
        self._vC = vC
        self._discriminant = discriminant
        F = self.F
        if F.signature()[1] != 1:
            raise ValueError("The base field must have exactly one complex place")
        a, b = B.invariants()
        if any(v(a) > 0 or v(b) > 0 for v in F.real_embeddings()):
            raise ValueError("The algebra must be ramified at all the real places")

    def complex_place(self, bits):
        from sage.rings.complex_mpfr import ComplexField

        CC = ComplexField(bits)
        if self._vC is not None:
            return self._vC
        embs = [v for v in self.F.embeddings(CC) if v(self.F.gen()).imag() > 0]
        return embs[0]

    def discriminant_norm(self):
        if self._discriminant is not None:
            return ZZ(self._discriminant)
        D = self.B.discriminant()
        return ZZ(D.norm()) if hasattr(D, "norm") else ZZ(D)

    def ramified_primes_norms(self):
        D = self.B.discriminant()
        return [ZZ(P.norm()) for P, _ in self.F.ideal(D).factor()]

    def is_maximal(self):
        return self.maximal is None


class _Embedding:
    r"""
    The map from the order to `M_2(\mathbb{H})` (Page's ``KleinianInjection``).
    """

    def __init__(self, ctx, data):
        from sage.rings.complex_mpfr import ComplexField

        self.ctx = ctx
        self.data = data
        bits = ctx.bits
        CC = ComplexField(bits)
        self.vC = data.complex_place(bits)
        a, b = data.B.invariants()
        sa = CC(self.vC(a)).sqrt()
        bb = CC(self.vC(b))
        self.sa = self._c(sa)
        self.bb = self._c(bb)
        self.bsa = self.bb * self.sa
        x, y, t = (
            ctx.R(c)
            for c in [QQ(data.center[0]), QQ(data.center[1]), QQ(data.center[2])]
        )
        aa = mpc(x, y)
        st = gmpy2.sqrt(t)
        self.P = (mpc(st), aa / st, mpc(0), mpc(1 / st))
        self.Pinv = (mpc(1 / st), -aa / st, mpc(0), mpc(st))
        self.real_places = [v for v in data.F.real_embeddings(prec=bits)]
        self._cache = {}

    @staticmethod
    def _c(z):
        return mpc(mpfr(z.real()), mpfr(z.imag()))

    def _cf(self, x):
        return self._c(self.vC(x))

    def complex_matrix(self, x, normalize):
        c = [self._cf(o) for o in x.coefficient_tuple()]
        x1, x2, x3, x4 = c
        M = (
            x1 + x2 * self.sa,
            x3 + x4 * self.sa,
            x3 * self.bb - x4 * self.bsa,
            x1 - x2 * self.sa,
        )
        m = _cmul(_cmul(self.Pinv, M), self.P)
        if normalize and x.reduced_norm() != 1:
            det = m[0] * m[3] - m[1] * m[2]
            s = 1 / gmpy2.sqrt(det)
            m = tuple(s * o for o in m)
        return m

    def matrix(self, x, normalize=True):
        r"""
        The matrix in `M_2(\mathbb{H})` of ``x`` acting on the unit ball.
        """
        key = (_key(x), normalize)
        try:
            return self._cache[key]
        except KeyError:
            pass
        m = self.complex_matrix(x, normalize)
        ans = cmatrix_to_ball(m)
        if len(self._cache) < 100000:
            self._cache[key] = ans
        return ans


def _cmul(m, n):
    return (
        m[0] * n[0] + m[1] * n[2],
        m[0] * n[1] + m[1] * n[3],
        m[2] * n[0] + m[3] * n[2],
        m[2] * n[1] + m[3] * n[3],
    )


def cmatrix_to_ball(m):
    r"""
    Convert a complex 2x2 matrix acting on upper half space into the
    corresponding matrix over the quaternions acting on the unit ball.
    """
    z = mpfr(0)
    j = (z, z, mpfr(1), z)
    a, b, c, d = ((o.real, o.imag, z, z) for o in m)
    half = mpfr(1) / 2
    A = qscal(half, qadd(qadd(a, qconj(d)), qmul(qsub(b, qconj(c)), j)))
    B = qscal(half, qadd(qadd(b, qconj(c)), qmul(qsub(a, qconj(d)), j)))
    C = qscal(half, qadd(qadd(c, qconj(b)), qmul(qsub(d, qconj(a)), j)))
    D = qscal(half, qadd(qadd(d, qconj(a)), qmul(qsub(c, qconj(b)), j)))
    return (A, B, C, D)


def isometric_sphere(emb, g):
    m = emb.matrix(g)
    C, D = m[2], m[3]
    n = sqrnorm(C)
    if n <= 0:
        raise ValueError("This element has no isometric sphere.")
    center = point(qscal(-1, qmul(qinv(C), D)))
    return Sphere(center, 1 / gmpy2.sqrt(n), g, m)


# ---------------------------------------------------------------------------
# Reduction
# ---------------------------------------------------------------------------


def reduce_point(ctx, emb, z, boundary, word=True, evaluate=True):
    r"""
    Reduce ``z`` into the exterior domain with faces ``boundary``.
    Returns ``(z', deltaword, delta, length)`` with ``z' = delta * z``.
    """
    B = boundary[0].g.parent()
    eps12 = ctx.eps12
    deltaword = []
    delta = B.one()
    length = 0
    while True:
        i0 = None
        d = mpfr(1)
        for i, S in enumerate(boundary):
            d1 = sqrnorm(qsub(z, S.center)) / S.radius**2
            if d >= (1 + eps12) * d1:
                d = d1
                i0 = i
        if i0 is None:
            break
        S = boundary[i0]
        z = action(ctx, S.matrix, z)
        if word:
            deltaword.append(i0)
        if evaluate:
            delta = S.g * delta
        length += 1
        g = S.g
        if not word and g.reduced_trace() ** 2 == 4 * g.reduced_norm():
            gg = g
            zz = z
            while True:
                z = zz
                gg = gg**2
                zz = action(ctx, emb.matrix(gg), z)
                delta = gg * delta
                if delta_dist(z, qzero()) <= (1 + eps12) * delta_dist(zz, qzero()):
                    break
            delta = gg**-1 * delta
    deltaword.reverse()
    return z, deltaword, delta, length


def reduce_element(ctx, emb, gamma, boundary, z=None, word=True, evaluate=True):
    if z is None:
        z = qzero()
    z0 = action(ctx, emb.matrix(gamma), z)
    z1, deltaword, delta, length = reduce_point(ctx, emb, z0, boundary, word, evaluate)
    return deltaword, delta, z1, length


# ---------------------------------------------------------------------------
# Enumeration
# ---------------------------------------------------------------------------


def _definite_gram(ctx, emb, data, basis, center1, facteur, balance):
    r"""
    Gram matrix (twice the quadratic form, as in Magma) of
    ``facteur * (|m_11|^2 + |m_12|^2 + balance * sum_{v real} v(nrd x))``
    where ``m`` is the matrix of ``x`` conjugated so that it measures the
    displacement of ``center1``.
    """
    n = len(basis)
    h1 = zero_to_p(ctx, center1)[0]
    h2i = zero_to_p(ctx, qzero())[1]
    mats = [mmul(mmul(h2i, emb.matrix(x, normalize=False)), h1) for x in basis]
    rows = [qadd(qscal(0, m[0]), m[0]) + m[1] for m in mats]  # 8 real coordinates
    G = [[mpfr(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(i, n):
            s = sum(rows[i][k] * rows[j][k] for k in range(8))
            G[i][j] = G[j][i] = 2 * facteur * s
    if balance != 0:
        a, b = data.B.invariants()
        for v in emb.real_places:
            av, bv = mpfr(v(a)), mpfr(v(b))
            D = [mpfr(1), -av, -bv, av * bv]
            coeffs = [[mpfr(v(c)) for c in x.coefficient_tuple()] for x in basis]
            for i in range(n):
                for j in range(i, n):
                    s = sum(D[k] * coeffs[i][k] * coeffs[j][k] for k in range(4))
                    G[i][j] += 2 * facteur * balance * s
                    if j != i:
                        G[j][i] = G[i][j]
    return G


def _short_vectors(G, bound, maxcount):
    from sage.libs.pari import pari

    n = len(G)
    Gp = pari.matrix(n, n, [pari(str(G[i][j])) for i in range(n) for j in range(n)])
    try:
        res = pari.qfminim(Gp, pari(str(bound)), maxcount, 2)
    except Exception:
        return []
    return [[ZZ(c) for c in v] for v in res[2]]


class _EnumState:
    pass


def _process_vector(st, x, allowsq):
    B = st.data.B
    if _isscalar(x):
        return
    nx = x.reduced_norm()
    if nx == 0:
        return
    F = st.data.F
    if abs(F(nx).norm()) == 1:
        if nx == 1 or (allowsq and F(nx).is_square()):
            if nx != 1:
                x = x / F(nx).sqrt()
            key = _key(x)
            if key not in st.enum_keys and st.data.contains(x):
                st.enum_keys.add(key)
                st.enum.append(x)
                st.partialgpelt += 1
        elif allowsq and st.grouptype >= 2:
            key = _key(x)
            if key not in st.enum_keys:
                st.enum_keys.add(key)
                st.enum.append(x)


def _enumerate_ball(st, basis, G, allowsq):
    maxvenum = 1000
    vecs = _short_vectors(G, st.stepu, maxvenum + 2)
    partialvect = 0
    for v in vecs:
        x = sum((c * o for c, o in zip(v, basis)), st.data.B(0))
        partialvect += 1
        _process_vector(st, x, allowsq)
        if partialvect >= maxvenum:
            break
    # adapt the step (Page's heuristic)
    da = st.divadapt
    if partialvect >= 900:
        st.stepu /= (100 + 5 / da) / 100
    if partialvect >= 200:
        st.stepu /= (100 + 2 / da) / 100
    if partialvect >= 60:
        st.stepu /= (100 + 1 / da) / 100
    if partialvect <= 1:
        st.stepu *= (100 + 7 / da) / 100
    if partialvect <= 10:
        st.stepu *= (100 + 4 / da) / 100
    if partialvect <= 20:
        st.stepu *= (100 + 1 / da) / 100
    st.divadapt += mpfr(1) / 9
    st.totalvect += partialvect


# ---------------------------------------------------------------------------
# Covolume
# ---------------------------------------------------------------------------


def covolume(data, prec_bits=200):
    r"""
    Covolume of the norm one group (modulo `\pm 1`) of a maximal order.
    """
    from sage.libs.pari import pari
    from sage.rings.real_mpfr import RealField

    F = data.F
    RRf = RealField(prec_bits)
    pol = F.defining_polynomial().change_ring(QQ)
    old = pari.default("realprecision")
    pari.set_real_precision(int(prec_bits * 0.302) + 5)
    L = pari.lfuncreate(pari(pol).subst(pol.variable_name(), "y"))
    zK2 = RRf(pari.lfun(L, 2).real())
    pari.set_real_precision(old)
    DK = RRf(ZZ(F.discriminant()).abs())
    phi = 1
    for nP in data.ramified_primes_norms():
        phi *= nP - 1
    n = F.degree()
    pi = RRf.pi()
    return DK ** (RRf(3) / 2) * zK2 * phi / (4 * pi**2) ** (n - 1)


def unit_index(F):
    r"""
    `[U^+ : U^2]` where `U^+` are the units positive at all real places.
    """
    U = F.unit_group()
    gens = U.gens_values()
    real = F.real_embeddings()
    # units mod squares form an F_2 vector space; count those totally positive
    from itertools import product

    count = 0
    for exps in product(range(2), repeat=len(gens)):
        u = F(1)
        for e, g in zip(exps, gens):
            if e:
                u *= g
        if all(v(u) > 0 for v in real):
            count += 1
    return count


# ---------------------------------------------------------------------------
# Main algorithm
# ---------------------------------------------------------------------------


def _add_nb(ctx, emb, g, F, FE, IE, G):
    G[_key(g)] = g
    update_exterior_domain(ctx, F, FE, IE, isometric_sphere(emb, g))
    gi = g**-1
    G[_key(gi)] = gi
    update_exterior_domain(ctx, F, FE, IE, isometric_sphere(emb, gi))


def _keep_same_group(ctx, emb, G, F, FE, IE, check_time):
    S = list(G.values())
    while True:
        add = 0
        for gamma in S:
            check_time()
            _, delta, _, _ = reduce_element(ctx, emb, gamma, F, word=False)
            gb = delta * gamma
            if not _isscalar(gb):
                add += 1
                update_exterior_domain(ctx, F, FE, IE, isometric_sphere(emb, gb))
                update_exterior_domain(ctx, F, FE, IE, isometric_sphere(emb, gb**-1))
        S = [f.g for f in F]
        if add == 0:
            break
    G.clear()
    for g in S:
        G[_key(g)] = g


def _check_pairing(ctx, emb, G, F, FE, IE, check_time):
    allpaired = True
    ie = 0
    while ie < len(FE):
        check_time()
        e = FE[ie]
        Sz = [z for z in end_points(e) if sqrnorm(z) < 1 - ctx.eps110]
        if len(Sz) < 2:
            theta = point_in_interval(ctx, e[1])
            Sz.append(point_in_circle(e[0], theta))
        if Sz and not is_in_exterior_domain(Sz[0], F, ctx.eps110):
            raise RuntimeError("Invalid edge in the exterior domain")
        for z1 in Sz:
            for f in sorted(e[2]):
                if f < len(F):
                    gamma = F[f].g
                    if not is_in_exterior_domain(
                        action(ctx, F[f].matrix, z1), F, ctx.eps110
                    ):
                        allpaired = False
                        _, delta, _, _ = reduce_element(
                            ctx, emb, gamma, F, z=z1, word=False
                        )
                        gamma = delta * gamma
                        if not _isscalar(gamma):
                            _add_nb(ctx, emb, gamma, F, FE, IE, G)
        ie += 1
    return allpaired


def _random_in_sphere(rng):
    while True:
        x, y, z = (2 * rng.random() - 1 for _ in range(3))
        w = x * x + y * y + z * z
        if 0 < w <= 1:
            w = w**0.5
            return mpfr(x / w), mpfr(y / w), mpfr(z / w)


def _random_hyperbolic_ball(ctx, rng, r):
    v = mpfr(rng.random()) * volume_ball(r)
    w = _random_in_sphere(rng)
    rh = radius_ball(v, ctx.eps110)
    ch = gmpy2.cosh(rh)
    re = gmpy2.sqrt((ch - 1) / (ch + 1))
    return (re * w[2], re * w[0], re * w[1], mpfr(0))


def _my_index(LG, contains, B):
    r"""
    Index, coset representatives and generators of the subgroup of the
    group generated by ``LG`` cut out by ``contains`` (Page's ``myIndex``).
    """
    S1 = [B.one()]
    S1new = [B.one()]
    S2 = {}
    while S1new:
        S1next = []
        for s in S1new:
            for g in LG:
                x = s * g
                xinv = x**-1
                insg = False
                for t in S1 + S1next:
                    txinv = t * xinv
                    if contains(txinv):
                        insg = True
                        y = txinv**-1
                        S2[_key(y)] = y
                if not insg:
                    S1next.append(x)
        S1 += S1next
        S1new = S1next
    return len(S1), S1, list(S2.values())


def normalized_basis(
    data,
    grouptype="NormOne",
    pr=60,
    pr_zetas=None,
    period_enum=100,
    initial_gens=None,
    nb_enum=0,
    max_time=0,
    seed=None,
    _index=1,
):
    r"""
    Compute a fundamental domain (Dirichlet domain centred at the image of
    ``data.center``) of the norm one group (``grouptype='NormOne'``) or the
    unit group (``grouptype='Units'``) of the order, modulo the centre.

    Returns a dictionary with the faces (spheres with attributes ``g`` and
    ``matrix``), the finite and infinite edges, the volume and covolume.
    """
    from sage.misc.prandom import getrandbits
    from sage.misc.timing import walltime

    if grouptype not in ("NormOne", "Units"):
        raise NotImplementedError(
            "Only the NormOne and Units group types are implemented"
        )
    gtype = 1 if grouptype == "NormOne" else 2
    if pr_zetas is None:
        pr_zetas = pr
    ctx = _Ctx(pr)
    rng = _pyrandom.Random(int(seed) if seed is not None else int(getrandbits(64)))
    t0 = walltime()

    def check_time():
        if max_time and walltime(t0) > max_time:
            raise KleinianTimeout("Timed out (%s sec) in normalized_basis" % max_time)

    B = data.B
    K = data.F
    degK = K.degree()
    omega = K.maximal_order().basis()[1]
    initial_gens = list(initial_gens or [])
    index = _index
    if not data.is_maximal():
        verbose("Computing for a maximal order first", level=1)
        resmax = normalized_basis(
            data.maximal,
            grouptype=grouptype,
            pr=pr,
            pr_zetas=pr_zetas,
            period_enum=period_enum,
            max_time=max_time,
            seed=int(rng.getrandbits(64)),
        )
        LG = [f.g for f in resmax["faces"]]
        index, _, genes = _my_index(LG, data.contains, B)
        verbose(
            "Subgroup has index %s, %s generators found" % (index, len(genes)), level=1
        )
        initial_gens += genes
        nb_enum = 1
    emb = _Embedding(ctx, data)

    indexunits = unit_index(K) if gtype == 2 else 1
    Covol = mpfr(covolume(data, ctx.bits)) * index / indexunits
    verbose("covolume %s" % Covol, level=2)

    db = 1
    for nP in data.ramified_primes_norms():
        db *= nP
    disc = abs(mpfr(int(ZZ(K.discriminant()) ** 4 * db**2)))

    NbEnum = nb_enum
    if NbEnum == 0:
        NbEnum = int(gmpy2.floor(mpfr("0.3") * Covol * gmpy2.log(2 + Covol))) + 1
    if degK == 2 and db == 1:
        NbEnum *= 2

    zetas = compute_zetas(pr_zetas)

    F, FE, IE = [], [], []
    G = {}
    factor = max(gmpy2.floor(disc * index / 5000), mpfr(1) / 2)
    propi = 6
    magicmul = mpfr(18) / 10
    stepu = 4 * factor * (magicmul * gmpy2.sqrt(disc) ** (mpfr(1) / (2 * degK)) + degK)
    balance = stepu / (4 * factor * degK)
    radenum = radius_ball(10 * max(Covol ** (2 + mpfr(1) / 10), mpfr(2)), ctx.eps110)

    st = _EnumState()
    st.data = data
    st.grouptype = gtype
    st.stepu = stepu
    st.divadapt = mpfr(9) / 10
    st.totalvect = 0
    st.totalgpelt = 0

    basis = data.basis
    allpaired = False
    Vol = mpfr(0)
    nochange = 0
    period = 1
    nbit = 0
    while True:
        nbit += 1
        check_time()
        period -= 1
        if period <= 0:
            st.enum = []
            st.enum_keys = set()
            ball = 1
            newelts = 0
            while True:
                check_time()
                allowsq = True
                if ball % 10 < propi and len(IE) != 0:
                    allowsq = False
                    enumcenter = _random_hyperbolic_ball(ctx, rng, radenum / 4)
                    ed = rng.randrange(len(IE))
                    theta = point_in_interval(ctx, IE[ed][1])
                    x = point_in_circle(IE[ed][0], theta)
                    x = qscal(1 - gmpy2.exp(-radenum), x)
                    hx = zero_to_p(ctx, x)[0]
                    enumcenter = action(ctx, hx, enumcenter)
                else:
                    enumcenter = _random_hyperbolic_ball(ctx, rng, radenum)
                Gram = _definite_gram(
                    ctx, emb, data, basis, enumcenter, 4 * factor, balance
                )
                st.partialgpelt = 0
                _enumerate_ball(st, basis, Gram, allowsq)
                newelts += st.partialgpelt
                st.totalgpelt += st.partialgpelt
                ball += 1
                if newelts >= NbEnum:
                    break
            enum = list(st.enum)
            for g in initial_gens:
                if not _isscalar(g):
                    enum.append(g)
            # "Bianchi helper": parabolic side pairings at the cusps
            for ied in list(IE):
                ieg = F[min(ied[2])].g
                if ieg.reduced_trace() ** 2 == 4 * ieg.reduced_norm():
                    c = ieg.coefficient_tuple()
                    x, y = c[0], c[2] - c[3]
                    for om in [K.one(), omega]:
                        gamma = B(
                            [
                                1,
                                x * y * om,
                                (y**2 - x**2) * om / 2,
                                (x**2 + y**2) * om / 2,
                            ]
                        )
                        enum.append(gamma)
                        _add_nb(ctx, emb, gamma, F, FE, IE, G)
            for gamma in enum:
                check_time()
                if F:
                    _, delta, _, _ = reduce_element(ctx, emb, gamma, F, word=False)
                    gb = delta * gamma
                else:
                    gb = gamma
                if not _isscalar(gb) and _key(gb) not in G:
                    _add_nb(ctx, emb, gb, F, FE, IE, G)
            period = period_enum
            _keep_same_group(ctx, emb, G, F, FE, IE, check_time)

        anf, anfe, anie = len(F), len(FE), len(IE)
        allpaired = _check_pairing(ctx, emb, G, F, FE, IE, check_time)
        if not allpaired and len(IE) == 0 and nochange <= 1:
            period += 1
        if len(F) == anf and len(FE) == anfe and len(IE) == anie:
            period = 1
            nochange += 1
            propi = min(propi + 1, 7)
        else:
            nochange = 0
            propi = max(propi - 1, 3)
        radenum += mpfr(1) / 6
        if FE:
            radenum += mpfr(1) / 5
        if nochange % 10 == 9:
            NbEnum *= 2
        if nochange % 5 == 4:
            NbEnum *= 2
        Vol = mpfr(0)
        if F and len(IE) <= 1 and allpaired:
            v = polyhedron_volume(ctx, F, FE, zetas)
            Vol = v if v is not None else mpfr(0)
        verbose(
            "iteration %s: #F = %s, #FE = %s, #IE = %s, paired = %s, Vol/Covol = %s"
            % (nbit, len(F), len(FE), len(IE), allpaired, float(Vol / Covol)),
            level=1,
        )
        if 0 < Vol < Covol * mpfr(9999) / 10000:
            verbose(
                "Error in the computation, rebuilding the exterior domain.", level=1
            )
            F2, FE2, IE2 = exterior_domain(ctx, list(F))
            F[:], FE[:], IE[:] = F2, FE2, IE2
            allpaired = False
        if (allpaired and abs(Vol / Covol - 1) < mpfr(1) / 1000) or abs(
            Vol / Covol - 1
        ) < mpfr(10) ** -10:
            break
    return {
        "faces": F,
        "finite_edges": FE,
        "infinite_edges": IE,
        "volume": Vol,
        "covolume": Covol,
        "index": index,
        "ctx": ctx,
        "embedding": emb,
        "iterations": nbit,
    }


# ---------------------------------------------------------------------------
# Presentation
# ---------------------------------------------------------------------------


def _order(g):
    if _isscalar(g):
        return 1
    if g.reduced_trace() ** 2 - 4 * g.reduced_norm() == 0:
        return 0
    o = 1
    gg = g
    while not _isscalar(gg):
        gg *= g
        o += 1
        if o > 1000:
            raise RuntimeError("Element of infinite order in an edge cycle")
    return o


def _compute_cycles(ctx, emb, F, FE, pairing):
    eps = ctx.eps13
    visited = [0] * len(FE)
    cycles = []
    words = []
    one = F[0].g.parent().one()
    reste = set(range(len(FE)))
    while reste:
        e = min(reste)
        if visited[e] != 0:
            reste.discard(e)
            continue
        cycle = []
        word = []
        e1 = e
        f = min(FE[e][2])
        transfo = one
        while True:
            cycle.append(e1)
            fs = sorted(FE[e1][2])
            f1 = fs[0]
            f2 = fs[1] if len(fs) > 1 else fs[0]
            if _isscalar(F[f].g * F[f1].g):
                f1 = f2
            f = f1
            transfo = F[f].g * transfo
            word.append(f)
            theta = point_in_interval(ctx, FE[e1][1])
            z = point_in_circle(FE[e1][0], theta)
            z1 = action(ctx, F[f].matrix, z)
            cands = sorted(reste & F[pairing[f]].edges)
            found = None
            for c in cands:
                cir = FE[c][0]
                if (
                    abs(sqrnorm(qsub(z1, cir.center)) - cir.radius**2) <= eps
                    and abs(scalar(qsub(z1, cir.center), cir.e3)) <= eps
                ):
                    found = c
                    break
            if found is None:
                raise RuntimeError("Did not find an adequate edge in the cycle")
            visited[e1] = f + 1
            e1 = found
            if e1 == e:
                break
        for c in cycle:
            reste.discard(c)
        cycles.append((cycle, transfo))
        words.append(word)
    return cycles, words


def presentation(faces, finite_edges, data=None, ctx=None, emb=None):
    r"""
    A presentation of the group with fundamental domain given by ``faces``
    and ``finite_edges`` (modulo the centre). Returns ``(gens, relations)``:
    ``gens[i]`` is the side pairing element of face ``i`` and each relation
    is a list of signed 1-based indices.
    """
    if ctx is None:
        ctx = _Ctx(60)
    F = faces
    FE = finite_edges
    nf = len(F)
    eps = ctx.eps12
    rels = []
    pairing = list(range(nf))
    order_ = sorted(range(nf), key=lambda i: sqrnorm(F[i].center))
    groups = []
    i = 0
    while i < nf:
        grp = [order_[i]]
        while (
            i + 1 < nf
            and abs(sqrnorm(F[order_[i]].center) - sqrnorm(F[order_[i + 1]].center))
            <= eps
        ):
            i += 1
            grp.append(order_[i])
        groups.append(grp)
        i += 1
    for grp in groups:
        for a in range(len(grp)):
            for b in range(a, len(grp)):
                i1, i2 = grp[a], grp[b]
                if _isscalar(F[i1].g * F[i2].g):
                    rels.append([i1 + 1, i2 + 1])
                    pairing[i1] = i2
                    pairing[i2] = i1
    cycles, words = _compute_cycles(ctx, emb, F, FE, pairing)
    for (cycle, transfo), w in zip(cycles, words):
        rel = [f + 1 for f in reversed(w)]
        o = _order(transfo)
        if o != 0:
            rels.append(rel * o)
    return [f.g for f in F], rels


def simplify_presentation(ngens, rels):
    r"""
    Simplify a presentation with GAP. Returns ``(new_rels, images, preimages)``
    where ``images[i]`` is the word in the new generators of the old
    generator ``i+1`` and ``preimages[j]`` is the word in the old generators
    of the new generator ``j+1``.
    """
    from sage.libs.gap.libgap import libgap

    Fr = libgap.FreeGroup(ngens)
    gens = Fr.GeneratorsOfGroup()

    def word(w):
        ans = Fr.One()
        for i in w:
            ans = ans * (gens[abs(i) - 1] if i > 0 else gens[abs(i) - 1] ** -1)
        return ans

    G = Fr / [word(r) for r in rels]
    iso = G.IsomorphismSimplifiedFpGroup()
    H = iso.Range()
    Ggens = G.GeneratorsOfGroup()
    Hgens = H.GeneratorsOfGroup()
    images = [
        [ZZ(o) for o in iso.Image(g).UnderlyingElement().LetterRepAssocWord()]
        for g in Ggens
    ]
    preimages = [
        [
            ZZ(o)
            for o in iso.PreImagesRepresentative(h)
            .UnderlyingElement()
            .LetterRepAssocWord()
        ]
        for h in Hgens
    ]
    new_rels = [[ZZ(o) for o in r.LetterRepAssocWord()] for r in H.RelatorsOfFpGroup()]
    return new_rels, images, preimages
