r'''
Additive version of ThetaOC.

The multiplicative implementation (ThetaOC) represents the theta function on
each ball by power series F_i(t) with F_i(0) = 1, and improves them with
products of power series. Here we store log F_i instead, so that products
become sums.

This is possible because all the series F_i are principal units: they are
products of factors (1 - x t) with |x| < 1 (the points of their divisors lie
in the interior of the balls, and the parameters send the complement of the
ball to the closed unit disk). So log F_i converges on the closed unit disk,
and composing with the action of the group (the matrices of get_action_data)
commutes with taking logarithms. The normalization F_i(0) = 1 becomes
log F_i(0) = 0.

What is not a principal unit is the finite rational part coming from the
words of length at most 1 (self.val). For it we compute, multiplicatively,
only the valuation and the first p-adic digit, which is then lifted with the
Teichmuller character. The rest (principal units) is again computed with
logarithms. Altogether, a value of theta is obtained as

    Theta(z) = pi^v * teichmuller(d) * exp(L),

where v and d (a residue field element) are computed multiplicatively and L
additively. This needs exp and log to be inverse isomorphisms between the
principal units and the maximal ideal, that is e < p - 1.
'''
from copy import copy

from sage.matrix.constructor import Matrix, matrix
from sage.misc.cachefunc import cached_function
from sage.misc.lazy_attribute import lazy_attribute
from sage.misc.misc_c import prod
from sage.functions.log import log
from sage.misc.verbose import verbose
from sage.modules.free_module_element import free_module_element as vector
from sage.rings.infinity import Infinity
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.structure.sage_object import SageObject

from .divisors import Divisors, DivisorsElement
from .meromorphic import MeromorphicFunctions, evalpoly
from .theta import eval_rat_dlog, pair_divisors


def _to_integer(x, pN):
    r'''
    An integer congruent to the p-adic integer x modulo pN.
    '''
    return ZZ(0) if x.is_zero() else ZZ(x.lift()) % pN


def _reduce_columns(R, mods):
    return [[int(R[b, k]) % int(mods[k]) for k in range(R.ncols())] for b in range(R.nrows())]


def _coordinate_moebius_entries(Ra, Rb, Rc, P, mods):
    r'''
    The nonzero entries (r, c, u) of the matrix whose row r contains the
    coefficients of zz^r, where zz = (b1 + a1 t) / (1 + c1 t) is a power series
    over the ring of integers O_K, given in coordinates: u is the list of
    coordinates of the entry, reduced modulo mods (see _OKCoordinates).

    The input are the matrices (as lists of rows) of the multiplication by a1,
    b1 and c1, acting on row vectors of coordinates. The rows are computed with
    zz^r = zz^(r-1) * (b1 + a1 t) / (1 + c1 t), that is, the coefficients satisfy
    u_k = b1 w_k + a1 w_(k-1) - c1 u_(k-1).
    '''
    from operator import mul
    d = len(mods)
    mods = [int(o) for o in mods]
    # Columns of the matrices, to compute the products with sum(map(mul, ...))
    columns = lambda R : [[R[b][k] for b in range(d)] for k in range(d)]
    Ca, Cb, Cc = columns(Ra), columns(Rb), columns(Rc)
    zero = [0] * d
    w = [[1] + [0] * (d - 1)] + [zero] * (P - 1) # zz^0 = 1
    entries = []
    for r in range(1, P):
        u = []
        prev_w = zero
        prev_u = zero
        nonzero = False
        for k in range(P):
            wk = w[k]
            if any(wk) or any(prev_w) or any(prev_u):
                uk = [(sum(map(mul, wk, Cb[j])) + sum(map(mul, prev_w, Ca[j])) - sum(map(mul, prev_u, Cc[j]))) % mods[j]
                      for j in range(d)]
                if any(uk):
                    nonzero = True
                    entries.append((r, k, uk))
            else:
                uk = zero
            u.append(uk)
            prev_w = wk
            prev_u = uk
        if not nonzero:
            break # All the remaining powers vanish
        w = u
    return entries


def _integer_moebius_matrix(a1, b1, c1, P, pN):
    r'''
    The P x P integer matrix whose row r contains the coefficients of zz^r
    modulo pN, where zz = (b1 + a1 t) / (1 + c1 t) (as in
    MeromorphicFunctions._action_matrix_moebius, but with integers).
    '''
    rows = [[1] + [0] * (P - 1)]
    w = rows[0]
    for _ in range(1, P):
        u = []
        prev_w = 0
        prev_u = 0
        for wk in w:
            uk = (b1 * wk + a1 * prev_w - c1 * prev_u) % pN
            prev_w = wk
            prev_u = uk
            u.append(uk)
        if not any(u):
            break # All the remaining powers vanish
        rows.append(u)
        w = u
    rows += [[0] * P for _ in range(P - len(rows))]
    return matrix(ZZ, rows)


def _check_integral(elements):
    if any(o.valuation() < 0 for o in elements if not o.is_zero()):
        raise ValueError('Not integral')


def _coordinates(x, F):
    r'''
    Coordinates of the integral element x of F in the basis given by
    _integral_basis(F).
    '''
    if F.absolute_degree() == 1:
        return [ZZ(0) if x.is_zero() else ZZ(x.lift())]
    if x.is_zero():
        return [ZZ(0)] * F.absolute_degree()
    try:
        # Unramified extensions (FLINT): x = p^v * poly(g)
        poly, v = x._flint_rep_abs()
        if v < 0:
            raise ValueError('Not integral')
        coeffs = poly.list()
        pv = ZZ(F.prime())**v
        return [ZZ(c) * pv for c in coeffs] + [ZZ(0)] * (F.absolute_degree() - len(coeffs))
    except AttributeError:
        pass
    B = F.base_ring()
    try:
        # Relative extensions: the underlying polynomial in the generator,
        # over the (floating point) base ring. Much faster than x.polynomial()
        coeffs = x._poly_rep().list()
    except AttributeError:
        coeffs = x.polynomial().list()
    ans = [c for a in coeffs for c in _coordinates(a, B)]
    return ans + [ZZ(0)] * (F.absolute_degree() - len(ans))


def _from_coordinates(c, F):
    r'''
    Inverse of _coordinates. The element is built from its coefficients (and
    not as a linear combination of the basis), so that it has the best
    precision that F can represent.
    '''
    if F.absolute_degree() == 1:
        return F(ZZ(c[0]))
    B = F.base_ring()
    n = F.relative_degree()
    k = len(c) // n
    gen = F.gen()
    # (F(list) loses precision for absolute Eisenstein extensions)
    return sum((F(_from_coordinates(c[i * k : (i + 1) * k], B)) * gen**i for i in range(n)), F(0))


def _integral_basis(F):
    r'''
    A Z_p-basis of the ring of integers of F: the products gen^i * b, where
    gen is the generator of F over its base ring and b runs over the basis of
    the base ring. For an Eisenstein extension of an unramified extension, it
    is (pi^i * g^j).
    '''
    if F.absolute_degree() == 1:
        return [F(1)]
    gen = F.gen()
    return [gen**i * F(b) for i in range(F.relative_degree()) for b in _integral_basis(F.base_ring())]


class _IntegerOperator(SageObject):
    r'''
    The linear map v |-> v * A on row vectors of integers (given as lists),
    for an integer matrix A whose column c is only needed modulo p^exps[c].

    There are three ways of computing the product:

    - 'dense': with FLINT (Sage's integer matrices).

    - 'sparse': with python integers, from the nonzero entries of A (column by
      column). Much faster than Sage's products when A is sparse.

    - 'banded': write each entry of A, and of v, as p^val times a smaller
      number. The rows and the columns of A are grouped in bands according
      to the valuations of their entries, and each block (row band, column
      band) is stored divided by p^mu, where mu is the smallest valuation of
      its entries, and reduced modulo p^(M - mu) (M being the largest
      exponent of its columns). In the product, the part of v corresponding
      to a row band is also divided by the power of p of its valuation
      beta, so that the block only needs to be computed modulo
      p^(M - mu - beta), with much smaller numbers (and not at all when
      mu + beta >= M). Integers modulo p^N cannot take advantage of the
      valuations of their entries by themselves, but this way the products
      only involve their significant digits.
    '''
    def __init__(self, A, p, exps, d, mode='auto', nbands=8, size=None):
        r'''
        A is either an integer matrix or a dictionary {(r, c) : A[r, c]} of
        its nonzero entries, in which case size = (number of rows, number of
        columns).
        '''
        if isinstance(A, dict):
            self._entries = A
            self._matrix = None
            self.nrows, self.ncols = size
        else:
            self._entries = None
            self._matrix = A
            self.nrows, self.ncols = A.nrows(), A.ncols()
        self.p = ZZ(p)
        self.exps = list(exps)
        if mode == 'auto':
            # In our tests (theta functions with series length 120 and 200),
            # FLINT was the fastest for Qp and the sparse products for all the
            # extensions, also when A is not very sparse. The banded products
            # are faster than the dense ones when the moduli are large, but
            # still slower than the sparse ones: the cost of Sage's products of
            # integer vectors and matrices per entry depends little on the
            # size of the entries.
            mode = 'dense' if d == 1 else 'sparse'
        self.mode = mode
        self.sparse = (mode == 'sparse')
        if mode == 'sparse':
            cols = [([], []) for _ in range(self.ncols)]
            for (r, c), a in sorted(self.entries.items(), key=lambda o : o[0][::-1]):
                cols[c][0].append(r)
                cols[c][1].append(int(a))
            self.cols = cols
        elif mode == 'banded':
            self._init_bands(nbands)

    @lazy_attribute
    def entries(self):
        if self._entries is None:
            self._entries = self._matrix.dict()
        return self._entries

    @lazy_attribute
    def A(self):
        if self._matrix is None:
            self._matrix = matrix(ZZ, self.nrows, self.ncols, self._entries)
        return self._matrix

    def _init_bands(self, nbands):
        p, exps = self.p, self.exps
        n, m = self.nrows, self.ncols
        entries = self.entries
        Mmax = max(exps)
        vals = {}
        rowval = [Infinity] * n
        colval = [Infinity] * m
        for (r, c), a in entries.items():
            v = ZZ(a).valuation(p)
            vals[r, c] = v
            rowval[r] = min(rowval[r], v)
            colval[c] = min(colval[c], v)
        width = max(1, -((-Mmax) // nbands))
        rowband = {r : v // width for r, v in enumerate(rowval) if v is not Infinity}
        colband = {c : v // width for c, v in enumerate(colval) if v is not Infinity}
        self.row_bands = {}
        for r, k in sorted(rowband.items()):
            self.row_bands.setdefault(k, []).append(r)
        self.col_bands = {}
        for c, l in sorted(colband.items()):
            self.col_bands.setdefault(l, []).append(c)
        rowpos = {r : i for rows in self.row_bands.values() for i, r in enumerate(rows)}
        colpos = {c : j for cols in self.col_bands.values() for j, c in enumerate(cols)}
        block_entries = {}
        for (r, c), v in vals.items():
            block_entries.setdefault((rowband[r], colband[c]), []).append((rowpos[r], colpos[c], r, c, v))
        self.col_exps = {l : max(exps[c] for c in cols) for l, cols in self.col_bands.items()}
        self.blocks = []
        for (k, l), ents in sorted(block_entries.items()):
            mu = min(o[4] for o in ents)
            M = self.col_exps[l]
            if mu >= M:
                continue
            pmu = p**mu
            mod = p**(M - mu)
            B = matrix(ZZ, len(self.row_bands[k]), len(self.col_bands[l]),
                       {(i, j) : (ZZ(entries[r, c]) // pmu) % mod for i, j, r, c, _ in ents})
            self.blocks.append((k, l, mu, M, B))

    def apply(self, v):
        if self.mode == 'sparse':
            return [sum([v[r] * a for r, a in zip(rows, vals)]) for rows, vals in self.cols]
        if self.mode == 'dense':
            return [int(o) for o in vector(ZZ, v) * self.A]
        p = self.p
        # The parts of v in each row band, divided by the power of p of their valuation
        chunks = {}
        for k, rows in self.row_bands.items():
            chunk = [v[r] for r in rows]
            nonzero = [o for o in chunk if o]
            if not nonzero:
                continue
            beta = min(ZZ(o).valuation(p) for o in nonzero)
            pb = p**beta
            chunks[k] = (beta, [ZZ(o) // pb for o in chunk])
        acc = {}
        for k, l, mu, M, B in self.blocks:
            try:
                beta, w = chunks[k]
            except KeyError:
                continue
            s = beta + mu
            if s >= M:
                continue
            mod = p**(M - s)
            prod = vector(ZZ, [o % mod for o in w]) * B
            ps = p**s
            try:
                acc[l] += ps * prod
            except KeyError:
                acc[l] = ps * prod
        ans = [0] * self.ncols
        for l, w in acc.items():
            for c, o in zip(self.col_bands[l], w):
                ans[c] = o
        return ans


class _PrecisionTracker(SageObject):
    r'''
    The data needed to keep track of the precision of the coefficients in
    _improve_integral: the nonzero entries of the action matrices, with their
    valuations and precisions. They are only computed when needed (when some
    input is not known to the full precision).
    '''
    def __init__(self, blocks, O, N, min_input_prec):
        # blocks: list of (row offset, column offset, {(r, c) : entry}, precision),
        # where the entries are integers (d = 1) or lists of coordinates
        self._blocks = blocks
        self._O = O
        self._N = int(N)
        self.min_input_prec = int(min(min_input_prec, N))

    @lazy_attribute
    def arrays(self):
        import numpy as np
        O, N = self._O, self._N
        p, e = O.p, int(O.e)
        src, dst, vals, precs = [], [], [], []
        for r0, c0, entries, prec in self._blocks:
            if not entries:
                continue
            positions = np.array(list(entries.keys()), dtype=np.int64)
            src.append(positions[:, 0] + r0)
            dst.append(positions[:, 1] + c0)
            if O.d == 1:
                vals.append(np.array([e * int(ZZ(x).valuation(p)) for x in entries.values()], dtype=np.int64))
            else:
                vals.append(np.array(O.element_valuations([c for u in entries.values() for c in u], N), dtype=np.int64))
            precs.append(np.full(len(entries), int(prec), dtype=np.int64))
        if not src:
            empty = np.zeros(0, dtype=np.int64)
            return empty, empty, empty, empty, empty, empty
        src, dst, vals, precs = [np.concatenate(o) for o in (src, dst, vals, precs)]
        # Sort by target, for np.minimum.reduceat
        order = np.argsort(dst, kind='stable')
        src, dst, vals, precs = src[order], dst[order], vals[order], precs[order]
        targets, starts = np.unique(dst, return_index=True)
        return src, dst, vals, precs, targets, starts


class _OKCoordinates(SageObject):
    r'''
    Coordinates of the elements of the ring of integers O_K of a p-adic field
    K in a Z_p-basis.

    The basis elements (pi^i * g^j) have valuations i, so that the elements of
    pi^N O_K are those whose coordinate (i, j) is divisible by
    p^ceil((N - i) / e). Since all the maps that we use are O_K-linear, we can
    reduce each coordinate modulo its own power of p without losing anything.
    '''
    def __init__(self, K):
        self.K = K
        self.p = ZZ(K.prime())
        self.e = ZZ(K.absolute_e())
        self.basis = _integral_basis(K)
        self.d = len(self.basis)
        self.offsets = [ZZ(b.valuation()) for b in self.basis]
        # For absolute Eisenstein extensions, Sage's x.polynomial() can be wrong
        # in the last digits when the absolute precision of x is larger than
        # the precision cap (as happens for elements of positive valuation).
        # So in that case we compute everything from the Eisenstein polynomial.
        self._absolute_eisenstein = (K.absolute_degree() > 1 and self.e > 1
                                     and K.base_ring().absolute_degree() == 1)
        if self._absolute_eisenstein:
            # Multiplication by pi: pi * pi^b = pi^(b+1), and pi^e = -sum_k f_k pi^k
            e = self.e
            f = [ZZ(c.lift()) for c in K.defining_polynomial().list()]
            Rpi = matrix(ZZ, e, e)
            for b in range(e - 1):
                Rpi[b, b + 1] = 1
            for k in range(e):
                Rpi[e - 1, k] = -f[k]
            self._Rpi_powers = {0 : matrix.identity(ZZ, e), 1 : Rpi}
            # The b-th basis element is pi^b
            self.R = [self._Rpi_power(b) for b in range(e)]
        else:
            # Matrix of the multiplication by the b-th basis element, acting on row vectors
            self.R = [matrix(ZZ, [self.coords(bb * b) for bb in self.basis]) for b in self.basis]

    def _Rpi_power(self, v):
        try:
            return self._Rpi_powers[v]
        except KeyError:
            ans = self._Rpi_powers[v] = self._Rpi_powers[1]**v
            return ans

    @lazy_attribute
    def _kind(self):
        K = self.K
        if K.absolute_degree() == 1:
            return 'Qp'
        if self._absolute_eisenstein:
            return 'absolute eisenstein'
        try:
            if self.e == 1:
                _ = K(1)._flint_rep_abs()
                return 'unramified'
            B = K.base_ring()
            if B.absolute_e() == 1 and B.absolute_degree() > 1:
                _ = K(1)._poly_rep().list()[0]._flint_rep_abs()
                return 'eisenstein over unramified'
        except AttributeError:
            pass
        return 'generic'

    def coords(self, x):
        kind = self._kind
        if x.is_zero():
            return [ZZ(0)] * self.d
        if kind == 'Qp':
            return [ZZ(x.lift())]
        if kind == 'unramified':
            return self._unramified_coords(x, self.d)
        if kind == 'eisenstein over unramified':
            # The underlying polynomial in pi, over the (floating point)
            # unramified ring. Much faster than x.polynomial()
            f = self.d // self.e
            ans = [c for a in x._poly_rep().list() for c in self._unramified_coords(a, f)]
            return ans + [ZZ(0)] * (self.d - len(ans))
        if kind == 'absolute eisenstein':
            v = x.valuation()
            if v > 0:
                # x = pi^v * u, and the precision of the unit u is at most the cap
                return list(vector(ZZ, _coordinates(x.unit_part(), self.K)) * self._Rpi_power(v))
        return _coordinates(x, self.K)

    def _unramified_coords(self, x, f):
        if x.is_zero():
            return [ZZ(0)] * f
        # x = p^v * poly(g)
        poly, v = x._flint_rep_abs()
        if v < 0:
            raise ValueError('Not integral')
        pv = self.p**v
        coeffs = poly.list()
        return [ZZ(c) * pv for c in coeffs] + [ZZ(0)] * (f - len(coeffs))

    def moduli(self, N):
        r'''
        The moduli of the coordinates of the elements of pi^N O_K.
        '''
        return [self.p**max(0, -((o - N) // self.e)) for o in self.offsets]

    def valuation(self, w, N):
        r'''
        Valuation of a vector of coordinates of elements (at most N).
        '''
        p, e, d = self.p, self.e, self.d
        return min([N] + [e * ZZ(c).valuation(p) + self.offsets[k % d] for k, c in enumerate(w) if c != 0])

    def element_valuations(self, w, N):
        r'''
        The valuations (at most N) of the elements whose coordinates are the
        consecutive blocks of d entries of w, as a list of python integers.
        '''
        p, e, d, offsets = self.p, int(self.e), self.d, self.offsets
        N = int(N)
        w = [ZZ(c) for c in w]
        if d == 1:
            return [e * int(c.valuation(p)) if c else N for c in w]
        ans = []
        for k in range(0, len(w), d):
            v = N
            for c, o in zip(w[k : k + d], offsets):
                if c:
                    v = min(v, e * int(c.valuation(p)) + int(o))
            ans.append(v)
        return ans

    def element(self, c, N):
        K = self.K
        kind = self._kind
        c = [ZZ(o) for o in c]
        if kind == 'Qp':
            return K(c[0]).add_bigoh(N)
        if kind == 'unramified':
            return K(c).add_bigoh(N)
        if kind == 'eisenstein over unramified':
            B = K.base_ring()
            f = self.d // self.e
            return K([B(c[i * f : (i + 1) * f]) for i in range(self.e)]).add_bigoh(N)
        return _from_coordinates(c, K).add_bigoh(N)


@cached_function
def _ok_coordinates(K):
    return _OKCoordinates(K)


@cached_function
def _inverse_integers(K, n):
    r'''
    The list [1/1, 1/2, ..., 1/n] of elements of K.
    '''
    return [None] + [K(QQ(1) / k) for k in range(1, n + 1)]


def _ramification_data(K):
    p = K.prime()
    try:
        e = K.absolute_e()
    except AttributeError:
        e = K.ramification_index()
    return p, ZZ(e)


def log_principal(u, prec=None):
    r'''
    Logarithm of a principal unit u (that is, u = 1 mod the maximal ideal),
    computed with the power series of log(1 + y).

    This is much faster than u.log() for extensions of extensions.
    '''
    K = u.parent()
    p, e = _ramification_data(K)
    y = u - 1
    if y.is_zero():
        return K(0).add_bigoh(u.precision_absolute())
    vy = y.valuation()
    if vy <= 0:
        raise ValueError('Not a principal unit')
    if prec is None:
        prec = u.precision_absolute()
    # The k-th term has valuation k * vy - e * v_p(k) >= f(k) = k * vy - e * log_p(k),
    # and f is increasing for k >= e / (vy * ln(p)). Stop when all the
    # remaining terms are negligible.
    lnp = float(log(p))
    kmax = 1
    while kmax * vy * lnp < e or (kmax + 1) * vy - e * float(log(kmax + 1)) / lnp < prec:
        kmax += 1
    inv = _inverse_integers(K, kmax)
    # Horner: log(1+y) = y (1 - y (1/2 - y (1/3 - ...)))
    ans = inv[kmax]
    for k in range(kmax - 1, 0, -1):
        ans = inv[k] - y * ans
    return (y * ans).add_bigoh(prec)


def exp_small(s, prec=None):
    r'''
    Exponential of s, which is assumed to have valuation > e / (p - 1).
    '''
    K = s.parent()
    p, e = _ramification_data(K)
    if prec is None:
        prec = min(s.precision_absolute(), K.precision_cap())
    if s.is_zero():
        return K(1).add_bigoh(prec)
    vs = s.valuation()
    if vs * (p - 1) <= e:
        raise ValueError('exp does not converge')
    # The k-th term has valuation k * vs - e * v_p(k!) >= k * vs - e * (k - 1) / (p - 1),
    # which is increasing in k. Stop when all the remaining terms are negligible.
    kmax = 1
    while (kmax + 1) * vs - e * QQ(kmax) / (p - 1) < prec:
        kmax += 1
    inv = _inverse_integers(K, kmax)
    # Horner: exp(s) = 1 + s (1 + s/2 (1 + s/3 (...)))
    ans = K(1)
    for k in range(kmax, 0, -1):
        ans = 1 + s * inv[k] * ans
    return ans.add_bigoh(prec)


def principal_part_log(w, q):
    r'''
    For a unit w, return log of its principal part w / teichmuller(w), computed
    as log(w^(q-1)) / (q-1), which avoids computing the Teichmuller lift.
    '''
    return log_principal(w**(q - 1)) / (q - 1)


class LogSeries(SageObject):
    r'''
    Power series log F(t), where t is the coordinate given by the parameter.
    '''
    def __init__(self, value, parameter):
        self._value = value
        self._parameter = parameter

    def evaluate(self, D, prec=None):
        a, b, c, d = self._parameter.list()
        phi = lambda Q: a / c if Q == Infinity else (a * Q + b) / (c * Q + d)
        if isinstance(D, DivisorsElement):
            return sum(n * evalpoly(self._value, phi(P), prec=prec) for P, n in D)
        else:
            return evalpoly(self._value, phi(D), prec=prec)

    def eval_dlog(self, D):
        r'''
        Logarithmic derivative of the corresponding multiplicative series,
        which here is just the derivative of the log-series.
        '''
        a, b, c, d = self._parameter.list()
        phiD = (a * D + b) / (c * D + d)
        try:
            der = self._der_coeffs
        except AttributeError:
            der = [k * o for k, o in enumerate(self._value)][1:]
            self._der_coeffs = der
        chainrule = (a * d - b * c) / (c * D + d) ** 2
        return chainrule * evalpoly(der, phiD)

    def act(self, action_data):
        r'''
        Log of the result of fast_act on the corresponding multiplicative
        series: compose with the Mobius transformation, and normalize so that
        the value at 0 is 0 (the multiplicative version divides by the value at
        0 instead).
        '''
        M, param = action_data
        ans = self._value * M
        ans[0] = 0
        return LogSeries(ans, param)

    def _repr_(self):
        return f'log-series {self._value}'


def log_series_of_divisor(D, parameter, prec):
    r'''
    log of the power series that MeromorphicFunctions(K, p, prec)(D, parameter)
    represents, namely the sum over (Q, n) in D of n * log(1 - x_Q t), where
    x_Q = (c Q + d) / (a Q + b).
    '''
    K = parameter.base_ring()
    a, b, c, d = parameter.list()
    coeffs = [K(0) for _ in range(prec)]
    for Q, n in D:
        x = c / a if Q == Infinity else (c * Q + d) / (a * Q + b)
        if x.valuation() <= 0:
            raise NotImplementedError('The series is not a principal unit')
        xk = x
        for k in range(1, prec):
            coeffs[k] += n * xk
            xk *= x
    inv = _inverse_integers(K, prec)
    coeffs = [K(0)] + [-inv[k] * coeffs[k] for k in range(1, prec)]
    return vector(K, [o.add_bigoh(prec) for o in coeffs])


class ThetaOCAdditive(SageObject):
    r'''
    Additive version of ThetaOC (see the module documentation).

    The interface is the same as that of ThetaOC (including initial_F, which
    is here a dictionary of lists of coefficients of log F_i (or of LogSeries,
    such as the Fnlist[-1] of a previous ThetaOCAdditive), and improve with
    tol), and evaluate returns the same values. evaluate_log returns the
    triple (v, d, L) such that the value is pi^v * teichmuller(d) * exp(L).
    '''
    def __init__(self, G, a=None, b=None, prec=None, **kwargs):
        K = kwargs.get("base_ring", None)
        if K is None:
            K = G.K
        self.K = K
        self.G = G
        self.p = G.pi
        p, e = _ramification_data(K)
        if e >= p - 1:
            raise NotImplementedError('The additive implementation needs e < p - 1')
        self.q = K.residue_field().cardinality()
        _ = G.generators()
        _ = G.balls()
        if prec is None:
            prec = K.precision_cap()
        self.prec = prec
        self.Div = Divisors(K)
        if b is None:
            D = self.Div(a)
            if D.degree() != 0:
                raise ValueError(
                    "Must specify a degree-0 divisor, or parameters a and b"
                )
        else:
            D = self.Div([(1, K(a)), (-1, K(b))])
        D = G.find_equivalent_divisor(D)
        self.a = a
        self.b = b
        # Only used to get the action data
        self.MM = MeromorphicFunctions(self.K, self.p, self.prec)
        params = G.parameters
        gens_ext = G.gens_extended()

        # Corresponding to words of length exactly 1
        D1dict = {i : g * D for i, g in gens_ext}

        # Corresponding to words of length exactly 2
        verbose("Computing L2", level=2)
        self.F2 = {i : LogSeries(log_series_of_divisor(sum(g * val for j, val in D1dict.items() if j != -i), tau, prec), tau)
                   for (i, g), tau in zip(gens_ext, params)}
        verbose("L2 computed", level=2)

        # self.val will contain the 0, 1 terms
        self.val = sum(D1dict.values(), D)
        initial_F = kwargs.get('initial_F', None)
        if initial_F is not None:
            self.Fnlist = [{i : LogSeries(self._to_vector(initial_F[i]), tau)
                            for (i, _), tau in zip(gens_ext, params)}]
        else:
            self.Fnlist = [copy(self.F2)]
        # How to compute the products with integer matrices (see _IntegerOperator)
        self._integral_mode = kwargs.get('integral_mode', 'auto')
        # Last term of the list implementation (None means Fnlist[-1]). Since
        # improve collapses Fnlist into its sum, it is needed to continue the
        # iteration in a later call to improve.
        self._last_term = None

    def _to_vector(self, data):
        K = self.K
        if isinstance(data, LogSeries):
            # e.g. Fnlist[-1] of a previous theta, as for ThetaOC
            data = data._value
        data = [K(o) for o in list(data)[:self.prec]]
        data += [K(0)] * (self.prec - len(data))
        data[0] = K(0)
        return vector(K, [o.add_bigoh(self.prec) for o in data])

    def _get_action_data(self):
        try:
            return self._action_data
        except AttributeError:
            pass
        gens_ext = self.G.gens_extended()
        params = self.G.parameters
        action_data = {}
        for (i, gi), tau in zip(gens_ext, params):
            for j, Fj in self.Fnlist[-1].items():
                if i != -j:
                    action_data[i, j] = (
                        self.MM.compute_action_data(gi, Fj._parameter, tau),
                        tau,
                    )
        self._action_data = action_data
        return action_data

    def _integral_data(self):
        r'''
        When all the data (the coefficients of the Mobius transformations of
        the action, and the series in F2) is integral, return what is needed
        to do the iteration with integer matrices (which is much faster than
        with generic matrices over K): the keys, the series length P, the
        iteration matrix (see _IntegerOperator), the vector of F2, the
        coordinates of O_K (see _OKCoordinates) and the data to keep track of
        the precision (see _PrecisionTracker). Otherwise return None.

        Each element of O_K is replaced by its coordinates in a Z_p-basis of
        O_K, and the multiplication by an element of O_K by an integer
        matrix. The matrices of the action are computed directly in these
        coordinates, with the recurrence that defines the powers of the
        Mobius transformations, and everything is computed modulo pi^P.
        '''
        try:
            return self._integral
        except AttributeError:
            pass
        try:
            self._integral = self._build_integral_data()
        except (TypeError, ValueError, ArithmeticError, NotImplementedError) as e:
            verbose(f'Not using integer matrices: {e}', level=2)
            self._integral = None
        return self._integral

    def _build_integral_data(self):
        K = self.K
        O = _ok_coordinates(K)
        keys = list(self.F2.keys())
        P = self.prec
        n = len(keys)
        d = O.d
        N = P
        # Build the integer matrices directly, without computing the action
        # matrices over K. They are those of get_action_data: row r contains
        # the coefficients of zz^r, where zz = (b1 + a1 t) / (1 + c1 t), for a1,
        # b1 and c1 integral.
        gens = dict(self.G.gens_extended())
        params = {i : F._parameter for i, F in self.F2.items()}
        moebius = {}
        for i in keys:
            for j in keys:
                if i == -j:
                    continue
                tau = params[i].change_ring(K)
                a, b, c, dd = (params[j] * (tau * gens[i]).adjugate()).list()
                if dd.is_zero():
                    raise ValueError('d = 0')
                coeffs = [a / dd, b / dd, c / dd]
                _check_integral(coeffs)
                moebius[i, j] = coeffs
        series = [o for F in self.F2.values() for o in F._value]
        _check_integral(series)
        # We compute modulo pi^P, and keep track of the precision of each
        # coefficient separately (see _improve_integral). The entries of the
        # action matrices are known to the precision of a1, b1 and c1, since
        # products and sums of integral elements do not lose absolute precision.
        mods = O.moduli(P)
        moebius_prec = {ij : min([P + 1] + [o.precision_absolute() for o in coeffs]) for ij, coeffs in moebius.items()}
        # For the precision tracking: the nonzero entries of the action
        # matrices, as (sources, targets, valuations, precision) for each pair
        track = []
        if d == 1:
            pN = mods[0]
            A = matrix(ZZ, n * P, n * P)
            for bi, i in enumerate(keys):
                for bj, j in enumerate(keys):
                    if i == -j:
                        continue
                    a1, b1, c1 = [int(_to_integer(o, pN)) for o in moebius[i, j]]
                    M = _integer_moebius_matrix(a1, b1, c1, P, int(pN))
                    # The normalization (value 0 at t = 0) is linear: kill column 0
                    M.set_column(0, [0] * P)
                    track.append((bj * P, bi * P, M.dict(), moebius_prec[i, j]))
                    # As row vectors: new_i = sum_j F_j * M_ij
                    A.set_block(bj * P, bi * P, M)
        else:
            # The multiplication by x is the integer matrix sum_b x_b R[b]. Compute
            # all of them at once: rows of X are coordinates, and the rows of
            # Rflat the matrices R[b], flattened.
            Rflat = matrix(ZZ, [Rb.list() for Rb in O.R])
            mult = lambda y : _reduce_columns(sum((ZZ(c) * Rb for c, Rb in zip(O.coords(y), O.R)), matrix(ZZ, d, d)), mods)
            positions = []
            X = []
            for bi, i in enumerate(keys):
                for bj, j in enumerate(keys):
                    if i == -j:
                        continue
                    Ra, Rb, Rc = [mult(o) for o in moebius[i, j]]
                    pair_entries = {}
                    # The coordinates of the entries of the action matrix
                    for r, c, u in _coordinate_moebius_entries(Ra, Rb, Rc, P, mods):
                        if c == 0:
                            continue # The normalization (value 0 at t = 0) kills column 0
                        # As row vectors: new_i = sum_j F_j * M_ij
                        positions.append(((bj * P + r) * d, (bi * P + c) * d))
                        X.append(u)
                        pair_entries[r, c] = u
                    track.append((bj * P, bi * P, pair_entries, moebius_prec[i, j]))
            Y = (matrix(ZZ, len(X), d, X) * Rflat).list() if X else []
            entries_A = {}
            k = 0
            for row, col in positions:
                for b1 in range(d):
                    for b2 in range(d):
                        val = Y[k] % mods[b2]
                        k += 1
                        if val:
                            entries_A[row + b1, col + b2] = val
            A = entries_A
        L2 = vector(ZZ, [c % m for i in keys for o in self.F2[i]._value for c, m in zip(O.coords(o), mods)])
        exps = [ZZ(md).valuation(O.p) if md > 1 else 0 for md in mods] * (n * P)
        import numpy as np
        L2prec = np.array([int(min(o.precision_absolute(), P)) for i in keys for o in self.F2[i]._value], dtype=np.int64)
        tracker = _PrecisionTracker(track, O, P, min(list(moebius_prec.values()) + [int(L2prec.min())]))
        return (keys, P, _IntegerOperator(A, O.p, exps, d, mode=self._integral_mode, size=(n * P * d, n * P * d)), L2, O, (tracker, L2prec))

    def _improve_integral(self, m, implementation, tol, data):
        r'''
        Same as improve, using integer matrices (see _integral_data). Return
        False if it cannot be used for the current approximation.
        '''
        import numpy as np
        keys, P, A, L2, O, (tracker, L2prec) = data
        K = self.K
        d = O.d
        p = K.prime()
        N = P
        if implementation == 'list' and self._last_term is not None:
            source = self._last_term
        else:
            source = self.Fnlist[-1]
        current = [o for i in keys for o in source[i]._value]
        summed = [o for i in keys for o in self.Fnlist[0][i]._value]
        try:
            _check_integral(current + summed)
        except ValueError:
            return False
        # We compute modulo pi^N (lifting the inputs), and keep track of the
        # precision of each coefficient as the p-adic elements would: the
        # error of a sum of products F_j[r] * M[r, c] has valuation at least
        # min(prec(F_j[r]) + val(M[r, c]), prec(M[r, c]) + val(F_j[r])).
        initial_prec = lambda elts : np.array([int(min(o.precision_absolute(), N)) for o in elts], dtype=np.int64)
        prec_v = initial_prec(current)
        prec_total = initial_prec(summed)
        # If all the inputs are known modulo pi^N, so are all the results
        tracking = min(int(prec_v.min()), int(prec_total.min()), tracker.min_input_prec) < N
        if tracking:
            src, dst, Mval, Mprec, targets, starts = tracker.arrays
        def propagate(precs, w):
            if not tracking:
                return precs
            vals = np.array(O.element_valuations(w, N), dtype=np.int64)
            ans = np.full(len(precs), int(N), dtype=np.int64)
            if len(src):
                # The entries are sorted by target
                q = np.minimum(precs[src] + Mval, Mprec + vals[src])
                ans[targets] = np.minimum(ans[targets], np.minimum.reduceat(q, starts))
            return ans
        size = lambda w : O.valuation(w, N)
        if d == 1 and A.mode == 'dense':
            # A single modulus: use Sage's integer vectors (FLINT)
            pN = O.moduli(N)[0]
            reduce = lambda w : vector(ZZ, w).apply_map(lambda o : o % pN)
            apply = lambda w : w * A.A
            add = lambda a, b : a + b
            sub = lambda a, b : a - b
        else:
            # Vectors are lists of python integers, coordinate k reduced modulo mods[k]
            mods = [int(o) for o in O.moduli(N)] * (len(keys) * P)
            reduce = lambda w : [o % md for o, md in zip(w, mods)]
            apply = A.apply
            add = lambda a, b : [x + y for x, y in zip(a, b)]
            sub = lambda a, b : [x - y for x, y in zip(a, b)]
        to_vector = lambda elts : reduce([int(c) for o in elts for c in O.coords(o)])
        def to_series(w, precs):
            return {i : LogSeries(vector(K, [O.element(w[(bi * P + r) * d : (bi * P + r + 1) * d], int(precs[bi * P + r]))
                                             for r in range(P)]),
                                  self.F2[i]._parameter)
                    for bi, i in enumerate(keys)}
        v = to_vector(current)
        total = to_vector(summed)
        L2 = reduce([int(o) for o in L2])
        self.last_change = None
        best = None
        stalled = 0
        for _ in range(m):
            if implementation == 'list':
                prec_v = propagate(prec_v, v)
                prec_total = np.minimum(prec_total, prec_v)
                v = reduce(apply(v))
                total = add(total, v)
                change = size(v)
                done = not any(v) # All the remaining terms vanish too
            else:
                prec_v = np.minimum(propagate(prec_v, v), L2prec)
                w = reduce(add(L2, apply(v)))
                change = size(sub(w, v))
                done = (w == v) # Fixed point reached
                v = w
            self.last_change = change
            if done:
                break
            if tol is not None:
                if best is None or change > best:
                    best = change
                    stalled = 0
                else:
                    stalled += 1
                if change >= tol or stalled >= 2:
                    break
        if implementation == 'list':
            self._last_term = to_series(v, prec_v)
            self.Fnlist = [to_series(reduce(total), prec_total)]
        else:
            self._last_term = None
            self.Fnlist = [to_series(v, prec_v)]
        return True

    def improve(self, m, **kwargs):
        r'''
        Same as ThetaOC.improve. In addition, it stops as soon as the
        iteration is exactly done (the new term of the list implementation is
        zero, or the fixed point iteration does not change anything).

        The keyword integral (True by default) selects whether to do the
        iteration with integer matrices when possible (see _integral_data),
        which is much faster: in our tests, from 2 to 15 times for Qp,
        unramified extensions and Eisenstein extensions of both.
        '''
        gens_ext = self.G.gens_extended()
        implementation = kwargs.get('implementation', 'list')
        tol = kwargs.get('tol', None)
        if implementation not in ['list', 'fixedpoint']:
            raise ValueError("implementation must be 'list' or 'fixedpoint'")
        if len(self.Fnlist) == 1 and kwargs.get('integral', True):
            data = self._integral_data()
            if data is not None and self._improve_integral(m, implementation, tol, data):
                return self
        action_data = self._get_action_data()
        prec = self.prec
        self.last_change = None
        best = None
        stalled = 0
        if implementation == 'list' and self._last_term is not None:
            source = self._last_term
        else:
            source = self.Fnlist[-1]
        for _ in range(m):
            tmp = {}
            for i, _ in gens_ext:
                vl = sum(Fj._value * action_data[i, j][0]
                         for j, Fj in source.items() if i != -j)
                vl[0] = 0
                tmp[i] = vector(self.K, [o.add_bigoh(prec) for o in vl])
            if implementation == 'list':
                new = {i : LogSeries(v, self.F2[i]._parameter) for i, v in tmp.items()}
                self.Fnlist.append(new)
                source = new
                change = min(min(o.valuation() for o in v) for v in tmp.values())
                # All the remaining terms vanish too
                done = all(o.is_zero() for v in tmp.values() for o in v)
            else:
                new = {i : LogSeries(tmp[i] + self.F2[i]._value, self.F2[i]._parameter) for i in tmp}
                old = self.Fnlist[-1]
                diffs = [new[i]._value - old[i]._value for i in new]
                change = min(min(o.valuation() for o in v) for v in diffs)
                # Fixed point reached
                done = all(o.is_zero() for v in diffs for o in v)
                self.Fnlist = [new]
                source = new
            self.last_change = change
            if done:
                break
            if tol is not None:
                if best is None or change > best:
                    best = change
                    stalled = 0
                else:
                    stalled += 1
                if change >= tol or stalled >= 2:
                    break
        self._last_term = source if implementation == 'list' else None
        if len(self.Fnlist) > 1:
            self.Fnlist = [{ky : LogSeries(sum((F[ky]._value for F in self.Fnlist[1:]), self.Fnlist[0][ky]._value),
                                           self.Fnlist[0][ky]._parameter)
                            for ky in self.Fnlist[0]}]
        return self

    def _prepare_divisor(self, z):
        if not isinstance(z, DivisorsElement):
            z = self.Div([(1, z)])
        if z.degree() != 0:
            z -= self.Div([(z.degree(), Infinity)])
        return self.G.find_equivalent_divisor(z)

    def log_series_part(self, z, prec=None):
        r'''
        The sum of the log F_i evaluated at the divisor z (already in the
        fundamental domain).
        '''
        return sum(F.evaluate(z, prec) for FF in self.Fnlist for F in FF.values())

    def __call__(self, z, **kwargs):
        return self.evaluate(z, **kwargs)

    def evaluate(self, z, **kwargs):
        r'''
        Value of theta at z. The rational part is computed exactly, and the
        rest as the exponential of a sum of logarithms.
        '''
        z = self._prepare_divisor(z)
        prec = kwargs.get('prec', None)
        ans0 = pair_divisors(self.val, z)
        return ans0 * exp_small(self.log_series_part(z, prec))

    def eval_derivative(self, z, return_value=False):
        r'''
        Same as ThetaOC.eval_derivative.
        '''
        dlog = self.eval_dlog(z)
        z0 = self.G.to_fundamental_domain(z)[0]
        value = self.evaluate(z0)
        if return_value:
            return value * dlog, value
        else:
            return value * dlog

    def eval_dlog(self, z):
        r'''
        Same as ThetaOC.eval_dlog.
        '''
        if isinstance(z, DivisorsElement):
            raise NotImplementedError
        if not self.G.in_fundamental_domain(z):
            raise ValueError("z must be in the fundamental domain of G")
        z0, wd = self.G.to_fundamental_domain(z)
        if len(wd) > 0:
            gens = self.G.gens_extended(as_dict=True)
            g = prod((gens[i] for i in wd), gens[1].parent()(1)).adjugate()
            a, b, c, d = g.list()
            fact = (a * d - b * c) * (c * z + d) ** -2
        else:
            fact = 1
        valdlog = eval_rat_dlog(self.val, z0)
        fdlog = sum((f.eval_dlog(z0) for FF in self.Fnlist for f in FF.values()), valdlog)
        return fact * fdlog

    def evaluate_log(self, z, **kwargs):
        r'''
        Return (v, d, L) such that theta(z) = pi^v * teichmuller(d) * exp(L).

        Only the valuation v and the first digit d (an element of the residue
        field) are computed multiplicatively. L is a sum of logarithms.
        '''
        z = self._prepare_divisor(z)
        prec = kwargs.get('prec', None)
        K = self.K
        q = self.q
        v = 0
        d = K.residue_field()(1)
        L = self.log_series_part(z, prec)
        for P, n in self.val:
            if P is Infinity:
                continue
            for Q, m in z:
                if Q is Infinity:
                    continue
                diff = P - Q
                if diff == 0:
                    continue
                vi = diff.valuation()
                w = diff >> vi
                v += m * n * vi
                d *= w.residue()**(m * n)
                L += (m * n) * principal_part_log(w, q)
        return v, d, L

    def value_from_log(self, v, d, L):
        r'''
        Inverse of evaluate_log.
        '''
        K = self.K
        return K.uniformizer()**v * K.teichmuller(self._lift_residue(d)) * exp_small(L)

    def _lift_residue(self, d):
        K = self.K
        try:
            return K(d)
        except (TypeError, ValueError, NotImplementedError):
            pass
        # Lift through the unramified subfield
        F = K.base_ring()
        return K(F(d))
