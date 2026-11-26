r"""
Quaternion algebras and their orders through PARI.

This module replaces the Magma functionality used by the arithmetic groups:
maximal and Eichler orders, local splittings adapted to an order, elements of
prescribed norm or minimal polynomial, and (through Rickards' library, see
:mod:`darmonpoints.afuch`) fundamental domains and presentations of arithmetic
Fuchsian groups.

Orders are represented by square integer matrices whose *columns* are the
coordinates of a `\ZZ`-basis of the order in terms of the `\ZZ`-basis of the
maximal order stored by PARI's ``alginit`` (this is the convention of
``afuchinit``).

EXAMPLES::

    sage: from darmonpoints.quatorder import QuaternionAlgebraPari
    sage: QA = QuaternionAlgebraPari(QQ, -1, 3)
    sage: QA.B
    Quaternion Algebra (-1, 3) with base ring Rational Field
    sage: QA.B.discriminant()
    6
    sage: M = QA.eichler_order_matrix(5)
    sage: M.det()
    5
    sage: O = QA.order_basis(M)
    sage: QA.is_in_order(M, O[2] * O[3])
    True

A local splitting adapted to the Eichler order::

    sage: (I, J, K), phi = QA.local_splitting(M, 5, 1, 20)
    sage: I**2 == -1 and J**2 == 3 and I * J == K and J * I == -K
    True
    sage: iota = QA.local_embedding_function((I, J, K), phi)
    sage: all(iota(o).apply_map(lambda t: t.valuation() >= 0) == matrix(2, 2, [1]*4) for o in O)
    True
    sage: all(iota(o)[1, 0].valuation() >= 1 for o in O)
    True

Elements of given norm and given minimal polynomial::

    sage: x = QA.element_of_norm(M, 7)
    sage: x.reduced_norm().abs(), QA.is_in_order(M, x)
    (7, True)
    sage: y = QA.element_with_minpoly(QA.maximal_order_matrix(), 1, 5)
    sage: y.reduced_trace(), y.reduced_norm()
    (1, 5)
"""

from itertools import product

from sage.algebras.quatalg.quaternion_algebra import QuaternionAlgebra
from sage.arith.functions import lcm
from sage.libs.pari import pari
from sage.matrix.constructor import Matrix as matrix
from sage.misc.cachefunc import cached_method
from sage.misc.verbose import verbose
from sage.modules.free_module import FreeModule
from sage.modules.free_module_element import free_module_element as vector
from sage.rings.complex_mpfr import ComplexField
from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import Qp
from sage.rings.rational_field import QQ
from sage.rings.real_mpfr import RealField
from sage.structure.sage_object import SageObject

from .afuch import (
    afuchelts,
    afuchinit,
    afuchpresentation,
    afuchsignature,
    afuchspair,
    afuchvertices,
    afuchword,
    algab,
    algsplitoo,
)

# Aurel Page's GP code for Eichler orders (see darmonpoints/fdom/eichler.gp),
# with all local variables declared. Names are prefixed to avoid clashes in
# the shared PARI instance.
_GP_EICHLER = [
    r"dp_algfromcenter(A,x) = { my(y); y = vectorv(algdim(A,1)); y = algbasistoalg(A,y); y[1] = nfbasistoalg(algcenter(A),x); algalgtobasis(A,y); };",
    r"dp_algmodpr(A,pr) = { my(p,Ap,g,Q,pro,lif,map,mapi); p = pr.p; Ap = algtableinit(algmultable(A),p); g = dp_algfromcenter(A,pr.gen[2]); g = algtomatrix(Ap,g); g = matimagemod(g,p); [Q,pro,lif] = algquotient(Ap,g,1); [map,mapi] = algsplit(Q); [map*pro,lif*mapi] };",
    r"dp_eichleridempotent(A,pr) = { my(map,mapi,d,n,e); [map, mapi] = dp_algmodpr(A,pr); d = algdegree(A); n = pr.f; e = vectorv(n*d^2); for(i=1, d-1, e[1+n*(d+1)*i] = 1); mapi*e };",
    r"dp_eichlerprimepower(A,pr,k) = { my(e,p,polidem = 3*'x^2-2*'x^3,B,N,Me,Mzk,nf,prk,Mprk,i); p = pr.p; e = dp_eichleridempotent(A,pr); i = 1; while(i<k, e = algpoleval(A,polidem,e); i *= 2; e %= p^ceil(i/pr.e);); N = algdim(A,1); B = Vec(matid(N)); Me = Mat(vector(N,j,algmul(A,B[j],e))); nf = algcenter(A); Mzk = Mat([dp_algfromcenter(A,z) | z <- nf.zk]); prk = idealtwoelt(nf,idealpow(nf,pr,k)); Mprk = algtomatrix(A,dp_algfromcenter(A,prk[2]),1); mathnfmodid(matconcat([Me,Mzk,Mprk]),prk[1]) };",
]
# Filter the columns v of V by the reduced norm, without building quaternions:
# Qs[c] are integer matrices with den * nrd(sum v_i b_i) = sum_c (v~ Qs[c] v) y^c
# (power basis of the centre). mode 0: exact equality with tgt (the vector of
# den * coordinates); mode 1: |N_{F/Q}| equal to tgt (= |N(nrd)| * den^deg).
# If aff is nonzero, a coordinate 1 is appended to each v (affine lattices).
_GP_EICHLER.append(
    r"dp_nrdfilter(Qs, V, aff, pol, mode, tgt) = { my(res = List(), d = #Qs, cs, z = vector(#Qs), W, V1); if(#V == 0, return([])); V1 = if(aff, matconcat([V; vector(#V, j, 1)]), V); W = vector(d, c, Qs[c] * V1); for(j = 1, #V1, cs = vector(d, c, W[c][,j]~ * V1[,j]); if(cs == z, next); if(mode == 0, if(cs == tgt, listput(res, j)), if(abs(norm(Mod(Polrev(cs, 'y), pol))) == tgt, listput(res, j)))); Vec(res) };"
)
_gp_loaded = False


def _load_gp_code():
    global _gp_loaded
    if not _gp_loaded:
        for line in _GP_EICHLER:
            pari(line)
        _gp_loaded = True


def _zp_span_basis(vecs):
    r"""
    Return a 2x2 matrix whose columns are a `\ZZ_p`-basis of the
    `\ZZ_p`-span of the given vectors of `\QQ_p^2`.
    """
    vecs = [v for v in vecs if not v.is_zero()]
    c1 = min(
        (v for v in vecs if not v[0].is_zero()), key=lambda v: v[0].valuation()
    )
    reduced = [v - (v[0] / c1[0]) * c1 for v in vecs]
    c2 = min(
        (v for v in reduced if not v[1].is_zero()), key=lambda v: v[1].valuation()
    )
    return matrix(c1.parent().base_ring(), 2, 2, [c1[0], c2[0], c1[1], c2[1]])


def _initial_padic_splitting(a, b):
    r"""
    Matrices ``I, J`` over `\QQ_p` with ``I^2 = a``, ``J^2 = b``,
    ``IJ = -JI``. Assumes that `(a,b)_p` is split.
    """
    R = a.parent()
    p = R.prime()
    if a.is_square():
        r = a.sqrt()
        return matrix(R, 2, 2, [r, 0, 0, -r]), matrix(R, 2, 2, [0, b, 1, 0])
    if b.is_square():
        s = b.sqrt()
        return matrix(R, 2, 2, [0, a, 1, 0]), matrix(R, 2, 2, [s, 0, 0, -s])
    # Find u, v with u^2 - a v^2 = b
    for j in range(-4, 5):
        for k in range(1, p**2 + 1):
            v = R(k) * R(p) ** j
            t = b + a * v**2
            if not t.is_zero() and t.is_square():
                u = t.sqrt()
                return matrix(R, 2, 2, [0, a, 1, 0]), matrix(
                    R, 2, 2, [u, -a * v, v, -u]
                )
    raise RuntimeError("Could not find a local splitting (is the algebra split?)")


class QuaternionAlgebraPari(SageObject):
    r"""
    A quaternion algebra `B = (a,b)_F` together with its PARI counterpart.

    INPUT:

    - ``F`` -- ``QQ`` or a number field defined by a monic integral polynomial
    - ``a``, ``b`` -- nonzero elements of ``F``, with ``a`` not a square
    """

    def __init__(self, F, a, b):
        self.F = F
        a, b = F(a), F(b)
        self.B = QuaternionAlgebra(F, a, b)
        self._deg = 1 if F is QQ else F.degree()
        if F is QQ:
            nfpol = pari("y")
        else:
            f = F.defining_polynomial()
            if not (f.is_monic() and all(c in ZZ for c in f.list())):
                raise NotImplementedError(
                    "The base field must be defined by a monic integral polynomial"
                )
            nfpol = pari(f.change_ring(QQ)).subst(f.variable_name(), "y")
        self.nf = pari.nfinit(nfpol)
        self.A = pari.alginit(self.nf, [self._F_to_pari(a), self._F_to_pari(b)])
        ab = algab(self.A)
        if self._pari_to_F(ab[0]) != a or self._pari_to_F(ab[1]) != b:
            raise RuntimeError("PARI changed the Hilbert symbol presentation")
        n = 4 * self._deg
        self._dim = n
        self.Omax_basis = [
            self.B([self._pari_to_F(c) for c in self._basis_vector_to_1ijk(i)])
            for i in range(n)
        ]
        self._Omax_mat = matrix(QQ, n, n, [self._B_to_Qvector(o) for o in self.Omax_basis])
        self._Omax_mat_inv = self._Omax_mat.inverse()

    def _repr_(self):
        return "PARI quaternion algebra (%s, %s) over %s" % (
            self.B.invariants() + (self.F,)
        )

    # Conversions

    def _F_to_pari(self, x):
        x = self.F(x)
        if self.F is QQ:
            return pari(QQ(x))
        return pari(x.polynomial("y"))

    def _pari_to_F(self, z):
        z = pari(z)
        if z.type() == "t_POLMOD":
            z = z.lift()
        if z.type() == "t_POL":
            coeffs = [QQ(c) for c in z.Vecrev()]
            if self.F is QQ:
                assert len(coeffs) <= 1
                return QQ(coeffs[0]) if coeffs else QQ(0)
            coeffs += [0] * (self._deg - len(coeffs))
            return self.F(coeffs)
        return self.F(QQ(z))

    def _basis_vector_to_1ijk(self, i):
        from .afuch import algbasisto1ijk

        return list(algbasisto1ijk(self.A, pari.matid(self._dim)[i]))

    def _B_to_Qvector(self, x):
        if self.F is QQ:
            return [QQ(o) for o in x.coefficient_tuple()]
        return [u for o in x.coefficient_tuple() for u in o.list()]

    def to_basis(self, x):
        r"""
        Coordinates of ``x`` in the basis of the stored maximal order.
        """
        return vector(QQ, self._B_to_Qvector(self.B(x))) * self._Omax_mat_inv

    def to_pari(self, x):
        return pari(list(self.to_basis(x))).Col()

    def from_basis(self, v):
        return sum((QQ(c) * o for c, o in zip(v, self.Omax_basis)), self.B(0))

    def from_pari(self, v):
        return self.from_basis([QQ(c) for c in v])

    # Orders

    def maximal_order_matrix(self):
        return matrix(ZZ, self._dim, self._dim, 1)

    def order_basis(self, M):
        r"""
        The `\ZZ`-basis of the order with matrix ``M`` as elements of ``B``.
        """
        return [self.from_basis(c) for c in M.columns()]

    def order_matrix_from_basis(self, basis):
        r"""
        The HNF matrix of the lattice spanned by ``basis`` (elements of ``B``).
        """
        n = self._dim
        rows = [self.to_basis(x) for x in basis]
        L = FreeModule(QQ, n).span(rows, ZZ)
        return L.basis_matrix().transpose()

    def is_in_order(self, M, x):
        v = M.solve_right(self.to_basis(x))
        return all(c in ZZ for c in v)

    def _pari_ideal(self, N):
        if self.F is QQ:
            return pari.idealhnf(self.nf, ZZ(N))
        N = self.F.ideal(N)
        gens = [self._F_to_pari(g) for g in N.gens()]
        I = pari.idealhnf(self.nf, gens[0])
        for g in gens[1:]:
            I = pari.idealadd(self.nf, I, g)
        return I

    def eichler_order_matrix(self, N):
        r"""
        Matrix of an Eichler order of level ``N`` contained in the stored
        maximal order. ``N`` must be coprime to the discriminant.
        """
        _load_gp_code()
        n = self._dim
        fact = pari.idealfactor(self.nf, self._pari_ideal(N))
        M = self.maximal_order_matrix()
        for pr, e in zip(fact[0], fact[1]):
            Mp = pari("dp_eichlerprimepower")(self.A, pr, e)
            Mp = matrix(ZZ, n, n, [[ZZ(Mp[j][i]) for j in range(n)] for i in range(n)])
            M = self.intersect_orders(M, Mp)
        return M

    def intersect_orders(self, M1, M2):
        n = self._dim
        V = FreeModule(QQ, n)
        L1 = V.span(M1.columns(), ZZ)
        L2 = V.span(M2.columns(), ZZ)
        return L1.intersection(L2).basis_matrix().transpose()

    # Local splittings

    def local_splitting(self, M, P, e, prec, extra_prec=20):
        r"""
        A splitting `\iota: B \otimes F_P \to M_2(\QQ_p)` such that the order
        with matrix ``M`` (assumed Eichler of level `P^e` at `P`, inside the
        stored maximal order) maps to matrices in `M_2(\ZZ_p)` that are upper
        triangular modulo `p^e`.

        ``P`` must be a prime of degree one. Returns ``(I, J, K), F_to_local``.
        """
        F = self.F
        if F is QQ:
            p = ZZ(P)
        else:
            P = F.ideal(P)
            if P.residue_class_degree() != 1:
                raise NotImplementedError("Only primes of degree one are supported")
            p = P.smallest_integer()
        R = Qp(p, prec + extra_prec)
        if F is QQ:
            phi = QQ.hom([R.one()])
        else:
            gbar = ZZ(P.residue_field()(F.gen()))
            roots = [
                r
                for r, _ in F.defining_polynomial().change_ring(R).roots()
                if (r - gbar).valuation() > 0
            ]
            if len(roots) != 1:
                raise NotImplementedError("Could not determine the embedding F -> Qp")
            phi = F.hom([roots[0]], check=False)
        a, b = (phi(o) for o in self.B.invariants())
        I, J = _initial_padic_splitting(a, b)

        def iota(x, I=I, J=J):
            c = x.coefficient_tuple()
            return phi(c[0]) + phi(c[1]) * I + phi(c[2]) * J + phi(c[3]) * I * J

        # Make the maximal order map onto M_2(Z_p)
        v = vector(R, [1, 0])
        g = _zp_span_basis([iota(o) * v for o in self.Omax_basis])
        ginv = g.inverse()
        I, J = ginv * I * g, ginv * J * g
        # Make the order upper triangular modulo p^e
        if e > 0:
            mats = [iota(o, I, J) for o in self.order_basis(M)]
            h = self._stable_line_matrix(mats, p, e, R)
            hinv = h.inverse()
            I, J = hinv * I * h, hinv * J * h
        R0 = Qp(p, prec)
        I = I.change_ring(R0)
        J = J.change_ring(R0)
        if F is QQ:
            phi0 = QQ.hom([R0.one()])
        else:
            phi0 = F.hom([R0(phi(F.gen()))], check=False)
        return (I, J, I * J), phi0

    @staticmethod
    def _stable_line_matrix(mats, p, e, R):
        r"""
        Find a primitive `v_1 \in \ZZ_p^2` such that each matrix maps `v_1` into
        `\ZZ_p v_1` modulo `p^e`, and return ``[v_1 | w]`` in `GL_2(\ZZ_p)`.
        """

        def stable(v, k):
            # m v is in Z_p v mod p^k  <=>  det([m v | v]) = 0 mod p^k
            for m in mats:
                mv0 = m[0, 0] * v[0] + m[0, 1] * v[1]
                mv1 = m[1, 0] * v[0] + m[1, 1] * v[1]
                d = mv0 * v[1] - mv1 * v[0]
                if not d.is_zero() and d.valuation() < k:
                    return False
            return True

        cands = [(R(1), R(t)) for t in range(p)] + [(R(0), R(1))]
        cands = [v for v in cands if stable(v, 1)]
        for k in range(1, e):
            new = []
            for v in cands:
                for s in range(p):
                    if v[0] == 1:
                        w = (v[0], v[1] + R(s) * R(p) ** k)
                    else:
                        w = (v[0] + R(s) * R(p) ** k, v[1])
                    if stable(w, k + 1):
                        new.append(w)
            cands = new
        if len(cands) != 1:
            raise RuntimeError(
                "Found %s stable lines (expected exactly one)" % len(cands)
            )
        v = cands[0]
        if v[0] == 1:
            return matrix(R, 2, 2, [v[0], 0, v[1], 1])
        return matrix(R, 2, 2, [v[0], 1, v[1], 0])

    def local_embedding_function(self, IJK, phi):
        I, J, K = IJK

        def iota(x):
            c = x.coefficient_tuple()
            return phi(c[0]) + phi(c[1]) * I + phi(c[2]) * J + phi(c[3]) * K

        return iota

    # Archimedean data

    @cached_method
    def split_real_place_index(self):
        r"""
        Index (0-based, among real places sorted as in PARI) of the unique
        split real place, or ``None`` if there is none or more than one.
        """
        s = algsplitoo(self.A)
        return None if s == 0 else s - 1

    @cached_method
    def real_places(self, prec):
        r"""
        The real embeddings of ``F`` with real precision ``prec``, in PARI's
        order (increasing roots).
        """
        RR = RealField(prec)
        if self.F is QQ:
            return [QQ.hom(RR)]
        roots = sorted(self.F.defining_polynomial().roots(RR, multiplicities=False))
        return [self.F.hom([r], check=False) for r in roots]

    @cached_method
    def splitting_at_infinity(self, prec):
        r"""
        Return ``(phi, (1, I, J, K))`` with ``phi: F -> RR`` the split real
        place and ``I, J, K`` real matrices, matching the embedding used by
        Rickards' fundamental domain code.
        """
        idx = self.split_real_place_index()
        if idx is None:
            raise ValueError("The algebra is not split at exactly one real place")
        RR = RealField(prec)
        phi = self.real_places(prec)[idx]
        a, b = (phi(o) for o in self.B.invariants())
        if a > 0:
            r = a.sqrt()
            I = matrix(RR, 2, 2, [r, 0, 0, -r])
            J = matrix(RR, 2, 2, [0, b, 1, 0])
        else:
            s = b.sqrt()
            I = matrix(RR, 2, 2, [0, a, 1, 0])
            J = matrix(RR, 2, 2, [s, 0, 0, -s])
        return phi, (matrix(RR, 2, 2, 1), I, J, I * J)

    # Enumeration of elements

    def _majorant_gram(self, basis, prec, conj=None):
        r"""
        Gram matrix (in ``basis``) of a positive definite quadratic form `Q`
        with `Q(x) \ge 2|\sigma(\mathrm{nrd}(x))|` at the split real place and
        `Q(x) \ge \sigma(\mathrm{nrd}(x))` at the ramified real places.
        """
        RR = RealField(prec)
        n = len(basis)
        G = matrix(RR, n, n, 0)
        idx = self.split_real_place_index()
        places = self.real_places(prec)
        if self.F is not QQ and self.F.signature()[1] > 0:
            # Complex places: Frobenius norm of the splitting over C
            from sage.rings.complex_mpfr import ComplexField

            CC = ComplexField(prec)
            for v in self.F.embeddings(CC):
                if v(self.F.gen()).imag() <= 0:
                    continue
                a, b = (v(o) for o in self.B.invariants())
                sa = CC(a).sqrt()
                rows = []
                for x in basis:
                    c = [v(t) for t in x.coefficient_tuple()]
                    m = [c[0] + c[1] * sa, c[2] + c[3] * sa, b * (c[2] - c[3] * sa), c[0] - c[1] * sa]
                    if conj is not None:
                        # conj is a 2x2 complex matrix (a random "centre")
                        mm = conj.inverse() * matrix(CC, 2, 2, m) * conj
                        m = mm.list()
                    rows.append([u for z in m for u in (z.real(), z.imag())])
                L = matrix(RR, rows)
                G += L * L.transpose()
        for vi, sigma in enumerate(places):
            a, b = (sigma(o) for o in self.B.invariants())
            coeffs = [[sigma(c) for c in x.coefficient_tuple()] for x in basis]
            if vi == idx:
                _, (one, I, J, K) = self.splitting_at_infinity(prec)
                if conj is not None:
                    cinv = conj.inverse()
                    I, J, K = cinv * I * conj, cinv * J * conj, cinv * K * conj
                rows = []
                for c in coeffs:
                    m = c[0] * one + c[1] * I + c[2] * J + c[3] * K
                    rows.append(m.list())
                L = matrix(RR, rows)
                G += L * L.transpose()
            else:
                D = matrix(RR, 4, 4, [1, 0, 0, 0, 0, -a, 0, 0, 0, 0, -b, 0, 0, 0, 0, a * b])
                L = matrix(RR, coeffs)
                G += 2 * L * D * L.transpose()
        return G

    def short_vectors(self, basis, C, prec=200, conj=None, max_count=2000, max_count_limit=500000):
        r"""
        The coordinates (as columns of a PARI matrix) of the vectors `x` (up
        to sign) of the lattice spanned by ``basis`` with `Q(x) \le C`, for
        the majorant `Q` of :meth:`_majorant_gram`.

        PARI returns at most ``max_count`` vectors; if there are more, the
        enumeration is repeated with a larger count (up to
        ``max_count_limit``), so that no vector is silently skipped.
        """
        G = pari(self._majorant_gram(basis, prec, conj))
        while True:
            res = pari.qfminim(G, C, max_count, 2)
            vecs = res[2]
            if ZZ(res[0]) <= len(vecs) or max_count >= max_count_limit:
                break
            max_count = min(4 * max(max_count, ZZ(res[0])), max_count_limit)
        return vecs

    def _some_short_vectors(self, basis, C, count, prec=200, conj=None):
        r"""
        At most ``count`` of the vectors of :meth:`short_vectors` (those that
        PARI finds first), and whether these are all of them.
        """
        G = pari(self._majorant_gram(basis, prec, conj))
        res = pari.qfminim(G, C, count, 2)
        vecs = res[2]
        return vecs, ZZ(res[0]) <= len(vecs)

    def _vector_to_element(self, basis, v, affine=False):
        x = sum((ZZ(c) * o for c, o in zip(v, basis)), self.B(0))
        if affine:
            x += basis[-1]
        return x

    def short_elements(self, basis, C, prec=200, conj=None, max_count=2000, max_count_limit=500000):
        r"""
        Elements `x` (up to sign) of the lattice spanned by ``basis`` with
        `Q(x) \le C`, for the majorant `Q` of :meth:`_majorant_gram`.
        """
        vecs = self.short_vectors(basis, C, prec, conj, max_count, max_count_limit)
        return [self._vector_to_element(basis, vecs[j]) for j in range(len(vecs))]

    def _coords(self, z):
        z = self.F(z)
        return [QQ(z)] if self.F is QQ else list(z.list())

    def _nrd_forms(self, basis):
        r"""
        ``(Qs, den)``: integer matrices ``Qs[c]`` such that
        ``den * nrd(sum v_i basis[i])`` has power-basis coordinates
        ``v^T Qs[c] v``.
        """
        n = len(basis)
        d = self._deg
        nrds = [x.reduced_norm() for x in basis]
        M = [[None] * n for _ in range(n)]
        for i in range(n):
            M[i][i] = self._coords(nrds[i])
            for j in range(i + 1, n):
                cross = (basis[i] + basis[j]).reduced_norm() - nrds[i] - nrds[j]
                M[i][j] = M[j][i] = self._coords(cross / 2)
        den = lcm([QQ(c).denominator() for row in M for e in row for c in e] + [1])
        Qs = [
            matrix(ZZ, n, n, [den * M[i][j][c] for i in range(n) for j in range(n)])
            for c in range(d)
        ]
        return pari(Qs), ZZ(den)

    def _filter_by_norm(self, forms, vecs, target, absolute, affine=False):
        r"""
        Indices (0-based) of the columns of ``vecs`` whose element has reduced
        norm ``target`` (if ``absolute`` is ``False``) or reduced norm of
        absolute norm ``|target|`` (a rational number, if ``absolute`` is ``True``).
        """
        _load_gp_code()
        Qs, den = forms
        if absolute:
            tgt = QQ(target).abs() * den ** self._deg
            if tgt not in ZZ:
                # den * nrd(x) has integral coordinates, so no x has this norm
                return []
            tgt = pari(ZZ(tgt))
            mode = 1
        else:
            tgt = pari([den * c for c in self._coords(target)])
            mode = 0
        idx = pari("dp_nrdfilter")(Qs, vecs, 1 if affine else 0, self.nf.nf_get_pol(), mode, tgt)
        return [ZZ(j) - 1 for j in idx]

    def _norm_lower_bound(self, N, prec=53):
        r"""
        Lower bound for `Q(x)` when `\mathrm{nrd}(x)` generates the ideal `(N)`.
        """
        if self.F is QQ:
            return 2 * ZZ(N).abs()
        n = self._deg
        return 2 * n * RealField(prec)(QQ(N.norm()).abs()) ** (1 / n)

    def elements_of_norm(self, M, N, max_elements=1, conj=None, prec=200, growth=1.5, max_tries=40, exact=False):
        r"""
        Elements `x` of the order with matrix ``M`` such that
        `\mathrm{nrd}(x)` generates the same ideal as ``N`` (or, if ``exact``
        is ``True``, such that `\mathrm{nrd}(x) = N`).
        """
        F = self.F
        basis = self.order_basis(M)
        N = F(N)
        NI = ZZ(N).abs() if F is QQ else F.ideal(N)
        C = self._norm_lower_bound(N) * growth
        found = []
        forms = self._nrd_forms(basis)
        Nabs = ZZ(N).abs() if F is QQ else ZZ(N.norm()).abs()
        # Only a few elements are needed, so enumerate the short vectors in
        # batches (the lattice may have a huge number of vectors below the
        # bound), and only enlarge the batch if it was not enough.
        count, max_count = 2000, 500000
        for _ in range(max_tries):
            vecs, complete = self._some_short_vectors(basis, C, count, prec, conj)
            if exact:
                idx = self._filter_by_norm(forms, vecs, N, absolute=False)
            else:
                idx = self._filter_by_norm(forms, vecs, Nabs, absolute=True)
            for jj in idx:
                x = self._vector_to_element(basis, vecs[jj])
                nx = x.reduced_norm()
                if exact:
                    ok = nx == N
                else:
                    ok = (ZZ(nx).abs() == NI) if F is QQ else (F.ideal(nx) == NI)
                if ok and x not in found and -x not in found:
                    found.append(x)
                    if len(found) >= max_elements:
                        return found
            if not complete and count < max_count:
                count *= 4
            else:
                C *= growth
        if found:
            return found
        raise RuntimeError("No element of norm %s found" % N)

    def search_elements_of_norm(self, M, N, test, prec=200, growth=1.5, max_tries=30):
        r"""
        The first element `x` (by increasing majorant) of the order with
        matrix ``M`` such that `\mathrm{nrd}(x)` generates the ideal `(N)` and
        ``test(x)`` is true, or ``None``.
        """
        F = self.F
        N = F(N)
        NI = ZZ(N).abs() if F is QQ else F.ideal(N)
        basis = self.order_basis(M)
        C = self._norm_lower_bound(N) * growth
        seen = set()
        forms = self._nrd_forms(basis)
        Nabs = ZZ(N).abs() if F is QQ else ZZ(N.norm()).abs()
        count, max_count = 2000, 500000
        for _ in range(max_tries):
            vecs, complete = self._some_short_vectors(basis, C, count, prec)
            for jj in self._filter_by_norm(forms, vecs, Nabs, absolute=True):
                x = self._vector_to_element(basis, vecs[jj])
                key = tuple(tuple(c.list()) if hasattr(c, "list") else (c,) for c in x.coefficient_tuple())
                if key in seen:
                    continue
                seen.add(key)
                nx = x.reduced_norm()
                ok = (ZZ(nx).abs() == NI) if F is QQ else (F.ideal(nx) == NI)
                if ok:
                    for y in (x, -x):
                        if test(y):
                            return y
            if not complete and count < max_count:
                count *= 4
            else:
                C *= growth
        return None

    def element_of_norm(self, M, N, **kwargs):
        return self.elements_of_norm(M, N, max_elements=1, **kwargs)[0]

    def _trace_slice(self, M, t):
        r"""
        Return ``(L0, x0)``: a `\ZZ`-basis ``L0`` of the elements of reduced
        trace zero of the order with matrix ``M``, and an element ``x0`` of the
        order with reduced trace ``t`` (or ``None`` if there is none).
        """
        F = self.F
        basis = self.order_basis(M)
        deg = self._deg

        def coords(z):
            z = F(z)
            return [QQ(z)] if F is QQ else list(z.list())

        T = matrix(QQ, [coords(x.reduced_trace()) for x in basis])
        target = vector(QQ, coords(t))
        den = lcm([c.denominator() for c in T.list() + list(target)])
        A = (den * T).change_ring(ZZ)
        bvec = (den * target).change_ring(ZZ)
        L0 = [
            sum((ZZ(c) * o for c, o in zip(v, basis)), self.B(0))
            for v in A.left_kernel().basis()
        ]
        # Integral solution of x * A = bvec via the Smith form U * A * V = D
        D, U, V = A.smith_form()
        bV = bvec * V
        y = [ZZ(0)] * A.nrows()
        for i in range(min(D.nrows(), D.ncols())):
            d = D[i, i]
            if d == 0:
                if bV[i] != 0:
                    return L0, None
                continue
            if bV[i] % d != 0:
                return L0, None
            y[i] = bV[i] // d
        for i in range(min(D.nrows(), D.ncols()), D.ncols()):
            if bV[i] != 0:
                return L0, None
        xv = vector(ZZ, y) * U
        x0 = sum((ZZ(c) * o for c, o in zip(xv, basis)), self.B(0))
        assert x0.reduced_trace() == F(t)
        return L0, x0

    def element_with_minpoly(self, M, t, n, prec=200, growth=1.5, max_tries=40):
        r"""
        An element `x` of the order with matrix ``M`` with reduced trace ``t``
        and reduced norm ``n``.

        The search runs over the affine lattice of elements of trace ``t``
        (enumerating the lattice spanned by the trace-zero elements and one
        element of trace ``t``, and keeping the vectors whose last coordinate
        is `\pm 1`), after translating by an element of `O_F` so that the
        trace is small.
        """
        F = self.F
        t, n = F(t), F(n)
        # Translate by c in O_F so that the trace is small: if x has trace t
        # and norm n, then x - c has trace t - 2c and norm n - c*t + c^2.
        if F is QQ:
            c = (t / 2).round()
        else:
            OF = F.maximal_order()
            c = sum(
                (QQ(a).round() * b for a, b in zip(OF.coordinates(t / 2), OF.basis())),
                F(0),
            )
        t0, n0 = t - 2 * c, n - c * t + c * c
        L0, x0 = self._trace_slice(M, t0)
        if x0 is None:
            raise RuntimeError("No element of the order has reduced trace %s" % t0)
        # Q(x0 + y) = (y + u)^T G0 (y + u) + Q(x0) - u^T G0 u, where G0 is the
        # Gram matrix on L0 and G0 u = (B(l_i, x0))_i: enumerate the y close
        # to -u with PARI's qfcvp.
        k = len(L0)
        lower = 2 * self._norm_lower_bound(n0) + 1
        slice_forms = self._nrd_forms(L0 + [x0])

        def search(conj, C, maxcount):
            # Elements x0 + y (y in L0) with Q_conj(x0 + y) <= C
            Gfull = self._majorant_gram(L0 + [x0], prec, conj)
            G0 = Gfull.submatrix(0, 0, k, k)
            bvec = vector(Gfull.base_ring(), [Gfull[i, k] for i in range(k)])
            u = G0.solve_right(bvec)
            offset = Gfull[k, k] - u * G0 * u
            if C <= offset:
                return None
            # qfcvp needs an exact Gram matrix: use a scaled and rounded one
            # (the candidates are checked exactly anyway).
            scale = ZZ(2) ** 40
            G0p = pari(matrix(ZZ, k, k, [(scale * e).round() for e in G0.list()]))
            targetp = pari([QQ((-ui * scale).round()) / scale for ui in u]).Col()
            res = pari.qfcvp(G0p, targetp, ((C - offset) * scale).ceil(), maxcount, 0)
            vecs = res[2]
            for jj in self._filter_by_norm(slice_forms, vecs, n0, absolute=False, affine=True):
                y = self._vector_to_element(L0 + [x0], vecs[jj], affine=True)
                if y.reduced_norm() == n0:
                    return y + c
            return None

        # First: embed over F and conjugate into the order by principalizing
        # a left ideal (fast in practice). If that fails, search near the
        # minimum of the affine lattice of elements of the right trace (the
        # solutions form a conjugacy class, so they are short only if their
        # axis passes near the centre of the majorant).
        try:
            return self._element_with_minpoly_by_principalization(M, t, n, prec)
        except RuntimeError:
            pass
        C = lower
        for _ in range(max(4, max_tries)):
            ans = search(None, C, 20000)
            if ans is not None:
                return ans
            C *= growth
        raise RuntimeError("No element with trace %s and norm %s found" % (t, n))

    def _solve_norm_equation(self, e, m, flag=100):
        r"""
        ``(X, Y)`` in `F^2` with `X^2 - e Y^2 = m`, or ``None`` if PARI's
        ``rnfisnorm`` does not find a solution.
        """
        F = self.F
        e, m = F(e), F(m)
        if e.is_square():
            s = e.sqrt()
            return (1 + m) / 2, (m - 1) / (2 * s)
        den = lcm([QQ(c).denominator() for c in e.list()])
        e1 = e * den**2  # integral; Y = den * Y1
        T = pari.rnfisnorminit(self.nf.nf_get_pol(), pari("x^2") - self._F_to_pari(e1))
        res = pari.rnfisnorm(T, self._F_to_pari(m), flag)
        if res[1] != 1:
            return None
        sol = res[0].lift() if res[0].type() == "t_POLMOD" else res[0]
        X = self._pari_to_F(pari.polcoef(sol, 0, "x"))
        Y1 = self._pari_to_F(pari.polcoef(sol, 1, "x"))
        Y = Y1 * den
        if X**2 - e * Y**2 != m:
            return None
        return X, Y

    def _element_with_minpoly_by_principalization(self, M, t, n, prec=200, max_z=50):
        r"""
        An element of the order with matrix ``M`` with reduced trace ``t`` and
        reduced norm ``n``, found as follows: an element ``z`` of `B` with
        `z^2 = t^2 - 4n` gives ``x1 = (t + z)/2`` with the right minimal
        polynomial; ``I = O + O x1`` is a left `O`-ideal whose right order
        contains ``x1``; if ``I = O alpha`` then ``alpha x1 alpha^-1`` is in `O`.
        """
        from sage.schemes.plane_conics.constructor import Conic

        F = self.F
        a, b = self.B.invariants()
        i, j, k = self.B.gens()
        d = F(t) ** 2 - 4 * F(n)
        z = None
        # A pure quaternion z = X i + Y j + Z k with z^2 = a X^2 + b Y^2 - ab Z^2
        # = d: fix one coordinate to a small value and solve the resulting
        # norm equation (each choice gives different local conditions).
        if F is QQ:
            small = [QQ(c) / den for den in [1, 2] for c in range(-max_z, max_z + 1)]
        else:
            OFb = F.maximal_order().basis()
            small = []
            for bound in [0, 1, 2]:
                for cs in product(range(-bound, bound + 1), repeat=len(OFb)):
                    if max([abs(c) for c in cs] + [0]) != bound:
                        continue
                    z0 = sum((c * o for c, o in zip(cs, OFb)), F(0))
                    small += [z0, z0 / 2]
        real_places = F.real_embeddings() if F is not QQ else [QQ.hom(RealField(53))]

        def locally_solvable(e, c):
            # X^2 - e Y^2 = c is solvable iff (e, c)_v = 1 for all places v
            if F is QQ:
                return True  # Sage's conic solver over QQ decides it directly
            if any(F.hilbert_symbol(e, c, v) != 1 for v in real_places):
                return False
            bad = [P for P, _ in (F.ideal(2) * F.ideal(e) * F.ideal(c)).factor()]
            return all(F.hilbert_symbol(e, c, P) == 1 for P in bad)

        def solve(e, c):
            if e == 0 or c == 0 or not locally_solvable(e, c):
                return None
            if F is QQ:
                ok, pt = Conic(F, [1, -e, -c]).has_rational_point(point=True)
                if not ok or pt[2] == 0:
                    return None
                return pt[0] / pt[2], pt[1] / pt[2]
            return self._solve_norm_equation(e, c)

        z = None
        for s0 in small:
            # Z = s0: X^2 - (-b/a) Y^2 = (d + ab s0^2)/a
            sol = solve(-b / a, (d + a * b * s0**2) / a)
            if sol is not None:
                z = sol[0] * i + sol[1] * j + s0 * k
                break
            # X = s0: Y^2 - a Z^2 = (d - a s0^2)/b
            sol = solve(a, (d - a * s0**2) / b)
            if sol is not None:
                z = s0 * i + sol[0] * j + sol[1] * k
                break
            # Y = s0: X^2 - b Z^2 = (d - b s0^2)/a
            sol = solve(b, (d - b * s0**2) / a)
            if sol is not None:
                z = sol[0] * i + s0 * j + sol[1] * k
                break
        if z is None:
            raise RuntimeError("Could not embed the quadratic field in the algebra")
        assert z**2 == d
        x1 = (F(t) + z) / 2
        O = self.order_basis(M)
        Ibasis = O + [o * x1 for o in O]
        IM = self.order_matrix_from_basis(Ibasis)
        I = self.order_basis(IM)
        index = (IM.det() / M.det()).abs()
        target = index.sqrt()
        if target not in QQ:
            raise RuntimeError("Unexpected index of the ideal")

        I_forms = self._nrd_forms(I)

        def is_gen(x):
            nx = x.reduced_norm()
            return nx != 0 and QQ(nx.norm() if F is not QQ else nx).abs() == target

        alpha = None
        dg = self._deg
        C = RealField(53)(2 * dg) * RealField(53)(target) ** (RealField(53)(1) / dg) * 1.5
        for _ in range(60):
            vecs = self.short_vectors(I, C, prec)
            for jj in self._filter_by_norm(I_forms, vecs, target, absolute=True):
                x = self._vector_to_element(I, vecs[jj])
                if is_gen(x):
                    alpha = x
                    break
            if alpha is not None:
                break
            C *= 1.5
        if alpha is None:
            raise RuntimeError("Could not principalize the ideal")
        y = alpha * x1 * alpha**-1
        assert self.is_in_order(M, y)
        assert y.reduced_trace() == F(t) and y.reduced_norm() == F(n)
        return y

    def _totally_positive_associate(self, N):
        r"""
        A generator of `(N)` that is positive at every real place, or ``None``.
        """
        F = self.F
        if F is QQ:
            return QQ(N).abs()
        N = F(N)
        units = [F(u) for u in F.unit_group().gens_values()]
        places = self.real_places(53)
        for exps in product(range(2), repeat=len(units)):
            u = N
            for e, v in zip(exps, units):
                u *= v**e
            if all(s(u) > 0 for s in places):
                return u
        return None

    def normalizer_element_of_norm(self, M, N, timeout=60):
        r"""
        An element of the order with matrix ``M`` that normalizes it and whose
        reduced norm is a totally positive generator of `(N)` (for instance,
        an Atkin-Lehner element), found with Rickards' ``afuchfindoneelt``.
        Returns ``None`` if none is found within ``timeout`` seconds.
        """
        from cysignals.alarm import AlarmInterrupt, alarm, cancel_alarm

        from .afuch import afuchfindoneelt

        if self.split_real_place_index() is None:
            # Rickards' code only handles algebras split at exactly one
            # real place (it crashes otherwise)
            return None
        nm = self._totally_positive_associate(N)
        if nm is None:
            return None
        X = afuchinit(self.A, pari(M), 0, 0)
        try:
            alarm(timeout)
            e = afuchfindoneelt(X, self._F_to_pari(nm))
            cancel_alarm()
        except AlarmInterrupt:
            return None
        return self.from_pari(e)

    # Fuchsian groups

    def fuchsian_group_data(self, M, bitprec=128):
        r"""
        Fundamental domain and presentation of the norm one group of the
        order with matrix ``M``, computed with Rickards' algorithm.

        Returns a dictionary with keys:

        - ``X``: the PARI structure (needed by :meth:`word_problem`)
        - ``gens``: generators of the presentation (elements of ``B``)
        - ``relations``: relations as lists of signed 1-based indices; each
          multiplies out to a central element (``1`` or ``-1``)
        - ``side_elements``: the side pairing elements of the domain
        - ``side_pairing``: the side pairing (1-based)
        - ``signature``: ``(genus, elliptic orders, cusps)``
        - ``vertices``: vertices of the domain in the upper half plane
        """
        from cypari2.handle_error import PariError

        from .afuch import afuchmakefdom, afuchnewp

        CC = ComplexField(bitprec)
        pc = CC(RealField(bitprec).pi() / 8, 1 / 2)  # Rickards' default base point
        try:
            X = afuchinit(self.A, pari(M), 0, 1, bitprec)
        except PariError as err:
            if "base point" not in str(err):
                raise
            # The base point lies on a set of measure zero: try other ones
            X0 = afuchinit(self.A, pari(M), 0, 0, bitprec)
            for x0, y0 in [(QQ(3) / 7, QQ(5) / 9), (QQ(-2) / 11, QQ(7) / 13), (QQ(1) / 5, QQ(9) / 10), (QQ(5) / 17, QQ(3) / 7)]:
                try:
                    X = afuchmakefdom(afuchnewp(X0, pari(x0) + pari(y0) * pari("I")))
                    pc = CC(x0, y0)
                    break
                except PariError as err2:
                    if "base point" not in str(err2):
                        raise
            else:
                raise
        P = afuchpresentation(X)
        gens = [self.from_pari(g) for g in P[0]]
        rels = [[ZZ(o) for o in r] for r in P[1]]
        sides = [self.from_pari(g) for g in afuchelts(X)]
        sig = afuchsignature(X)
        signature = (ZZ(sig[0]), [ZZ(o) for o in sig[1]], ZZ(sig[2]))
        verts = []
        for w in afuchvertices(X, 1):
            w = CC(w.real().sage(), w.imag().sage())
            verts.append((pc - pc.conjugate() * w) / (1 - w))
        return {
            "X": X,
            "gens": gens,
            "relations": rels,
            "side_elements": sides,
            "side_pairing": [ZZ(o) for o in afuchspair(X)],
            "signature": signature,
            "vertices": verts,
            "center": pc,
        }

    def word_problem(self, X, x):
        r"""
        Write ``x`` (of norm one, in the order of ``X``) as a word in the
        generators of the presentation, up to sign.
        """
        return [ZZ(o) for o in afuchword(X, self.to_pari(x))]
