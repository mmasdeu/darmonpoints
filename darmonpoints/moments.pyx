# distutils: libraries = flint gmp
r"""
Fast computation of the matrices giving the action of `2 \times 2` matrices
on moments, as used by :class:`darmonpoints.ocmodule.OCVn`.
"""
from sage.libs.flint.types cimport fmpz, fmpz_poly_t, fmpz_t, slong, ulong
from sage.libs.gmp.types cimport mpz_t


# Declared here rather than cimported from ``sage.libs.flint.fmpz``, whose
# ``.pxd`` is not usable in some Sage installations (it cimports a missing
# ``fmpz_macros.pxd``).
cdef extern from "flint_wrap.h":
    void fmpz_init(fmpz_t f) noexcept
    void fmpz_clear(fmpz_t f) noexcept
    void fmpz_set_mpz(fmpz_t f, const mpz_t x) noexcept
    void fmpz_get_mpz(mpz_t x, const fmpz_t f) noexcept
    void fmpz_set(fmpz_t f, const fmpz_t g) noexcept
    void fmpz_one(fmpz_t f) noexcept
    void fmpz_neg(fmpz_t f1, const fmpz_t f2) noexcept
    void fmpz_mul(fmpz_t f, const fmpz_t g, const fmpz_t h) noexcept
    void fmpz_addmul(fmpz_t f, const fmpz_t g, const fmpz_t h) noexcept
    void fmpz_add(fmpz_t f, const fmpz_t g, const fmpz_t h) noexcept
    void fmpz_sub(fmpz_t f, const fmpz_t g, const fmpz_t h) noexcept
    void fmpz_submul(fmpz_t f, const fmpz_t g, const fmpz_t h) noexcept
    void fmpz_mul_ui(fmpz_t f, const fmpz_t g, ulong x) noexcept
    void fmpz_add_ui(fmpz_t f, const fmpz_t g, ulong x) noexcept
    void fmpz_zero(fmpz_t f) noexcept
    int fmpz_is_zero(const fmpz_t f) noexcept
    int fmpz_divisible(const fmpz_t f, const fmpz_t g) noexcept
    void fmpz_divexact(fmpz_t f, const fmpz_t g, const fmpz_t h) noexcept
    void fmpz_mod(fmpz_t f, const fmpz_t g, const fmpz_t h) noexcept
    int fmpz_invmod(fmpz_t f, const fmpz_t g, const fmpz_t h) noexcept
    void fmpz_pow_ui(fmpz_t f, const fmpz_t g, ulong x) noexcept
    void fmpz_set_ui(fmpz_t f, ulong val) noexcept
    fmpz * _fmpz_vec_init(slong len) noexcept
    void _fmpz_vec_clear(fmpz * vec, slong len) noexcept
    void _fmpz_vec_zero(fmpz * vec, slong len) noexcept

from sage.libs.flint.fmpz_mat_macros cimport fmpz_mat_entry
from sage.matrix.matrix_integer_dense cimport Matrix_integer_dense
from sage.rings.integer cimport Integer

from sage.matrix.matrix_space import MatrixSpace
from sage.rings.integer_ring import ZZ


def moebius_moment_matrix(a, b, c, d, N, slong depth):
    r"""
    Return the ``depth`` by ``depth`` integer matrix whose ``i``-th row holds
    the first ``depth`` coefficients of `((b + a z) / (d + c z))^i`, reduced
    modulo ``N`` (with entries in `[0, N)`).

    EXAMPLES::

        sage: from darmonpoints.moments import moebius_moment_matrix
        sage: moebius_moment_matrix(1, 2, 5, 3, 5^3, 3)
        [ 1  0  0]
        [84 27 80]
        [56 36 44]
        sage: R.<z> = PowerSeriesRing(Zmod(5^3), default_prec=3)
        sage: [((2 + z) / (3 + 5*z))^i for i in range(3)]
        [1, 84 + 27*z + 80*z^2 + O(z^3), 56 + 36*z + 44*z^2 + O(z^3)]

    The entry ``d`` must be invertible modulo ``N``::

        sage: moebius_moment_matrix(1, 2, 3, 13, 13^5, 4)
        Traceback (most recent call last):
        ...
        ZeroDivisionError: d is not invertible modulo N
    """
    cdef Integer NN = Integer(N)
    cdef Integer A = Integer(a) % NN
    cdef Integer B = Integer(b) % NN
    cdef Integer C = Integer(c) % NN
    cdef Integer D = Integer(d) % NN
    cdef fmpz_t fn, dinv, alpha, beta, gamma, tmp
    cdef slong i, j
    cdef Matrix_integer_dense M = MatrixSpace(ZZ, depth, depth)()
    if depth <= 0:
        return M
    fmpz_init(fn)
    fmpz_init(dinv)
    fmpz_init(alpha)
    fmpz_init(beta)
    fmpz_init(gamma)
    fmpz_init(tmp)
    try:
        fmpz_set_mpz(fn, NN.value)
        fmpz_set_mpz(tmp, D.value)
        if not fmpz_invmod(dinv, tmp, fn):
            raise ZeroDivisionError("d is not invertible modulo N")
        # alpha = a/d, beta = b/d, gamma = -c/d (mod N)
        fmpz_set_mpz(tmp, A.value)
        fmpz_mul(alpha, tmp, dinv)
        fmpz_mod(alpha, alpha, fn)
        fmpz_set_mpz(tmp, B.value)
        fmpz_mul(beta, tmp, dinv)
        fmpz_mod(beta, beta, fn)
        fmpz_set_mpz(tmp, C.value)
        fmpz_mul(gamma, tmp, dinv)
        fmpz_neg(gamma, gamma)
        fmpz_mod(gamma, gamma, fn)
        # Row i is the truncation of y_i = r^i, with r = (b + a z)/(d + c z).
        # From (d + c z) y_i = (b + a z) y_{i-1} we get the recurrence
        #   y_i[j] = beta y_{i-1}[j] + alpha y_{i-1}[j-1] + gamma y_i[j-1],
        # which only involves coefficients of index <= j, so truncation is exact.
        fmpz_one(fmpz_mat_entry(M._matrix, 0, 0))
        for i in range(1, depth):
            fmpz_mul(tmp, beta, fmpz_mat_entry(M._matrix, i - 1, 0))
            fmpz_mod(fmpz_mat_entry(M._matrix, i, 0), tmp, fn)
            for j in range(1, depth):
                fmpz_mul(tmp, beta, fmpz_mat_entry(M._matrix, i - 1, j))
                fmpz_addmul(tmp, alpha, fmpz_mat_entry(M._matrix, i - 1, j - 1))
                fmpz_addmul(tmp, gamma, fmpz_mat_entry(M._matrix, i, j - 1))
                fmpz_mod(fmpz_mat_entry(M._matrix, i, j), tmp, fn)
    finally:
        fmpz_clear(fn)
        fmpz_clear(dinv)
        fmpz_clear(alpha)
        fmpz_clear(beta)
        fmpz_clear(gamma)
        fmpz_clear(tmp)
    return M


def moebius_moment_accumulate(Matrix_integer_dense U, slong r0, slong c0, coeff,
                              a, b, c, d, p, slong n, slong depth):
    r"""
    Add ``coeff`` times the moment matrix of ``[[a, b], [c, d]]`` (as in
    :func:`moebius_moment_matrix`) to the ``depth`` by ``depth`` block of
    ``U`` starting at row ``r0`` and column ``c0``, with row ``i`` computed
    only modulo `p^{n - i}` (the entries of ``U`` are not reduced).

    This is the precision of the filtration of overconvergent distributions
    (the moment `i` is only meaningful modulo `p^{n - i}`). Modulo this
    filtration, the moment matrices are multiplicative: the moment matrix of
    `AB` is congruent to the product of those of `A` and `B`, when `A`, `B`
    have lower left entry divisible by `p` and lower right entry a unit.

    EXAMPLES::

        sage: from darmonpoints.moments import moebius_moment_matrix, moebius_moment_accumulate
        sage: p, n = 5, 4
        sage: M = moebius_moment_matrix(1, 2, 5, 3, p^n, n + 1)
        sage: U = matrix(ZZ, 7, 7)
        sage: moebius_moment_accumulate(U, 1, 2, 3, 1, 2, 5, 3, p, n, n + 1)
        sage: all((U[1 + i, 2 + j] - 3 * M[i, j]) % p^(n - i) == 0
        ....:     for i in range(n + 1) for j in range(n + 1))
        True
    """
    cdef Integer P = Integer(p)
    cdef Integer K = Integer(coeff)
    cdef Integer A = Integer(a)
    cdef Integer B = Integer(b)
    cdef Integer C = Integer(c)
    cdef Integer D = Integer(d)
    cdef fmpz_t fp, fn, mi, dinv, alpha, beta, gamma, al, be, ga, tmp, fk
    cdef fmpz * prev
    cdef fmpz * cur
    cdef fmpz * swap
    cdef slong i, j
    if depth <= 0:
        return
    if r0 < 0 or c0 < 0 or r0 + depth > U._nrows or c0 + depth > U._ncols:
        raise IndexError("block out of range")
    fmpz_init(fp)
    fmpz_init(fn)
    fmpz_init(mi)
    fmpz_init(dinv)
    fmpz_init(alpha)
    fmpz_init(beta)
    fmpz_init(gamma)
    fmpz_init(al)
    fmpz_init(be)
    fmpz_init(ga)
    fmpz_init(tmp)
    fmpz_init(fk)
    prev = _fmpz_vec_init(depth)
    cur = _fmpz_vec_init(depth)
    try:
        fmpz_set_mpz(fp, P.value)
        fmpz_pow_ui(fn, fp, n)
        fmpz_set_mpz(fk, K.value)
        fmpz_set_mpz(tmp, D.value)
        fmpz_mod(tmp, tmp, fn)
        if not fmpz_invmod(dinv, tmp, fn):
            raise ZeroDivisionError("d is not invertible modulo p^n")
        fmpz_set_mpz(tmp, A.value)
        fmpz_mul(alpha, tmp, dinv)
        fmpz_mod(alpha, alpha, fn)
        fmpz_set_mpz(tmp, B.value)
        fmpz_mul(beta, tmp, dinv)
        fmpz_mod(beta, beta, fn)
        fmpz_set_mpz(tmp, C.value)
        fmpz_mul(gamma, tmp, dinv)
        fmpz_neg(gamma, gamma)
        fmpz_mod(gamma, gamma, fn)
        # Row 0 is (1, 0, ..., 0)
        _fmpz_vec_zero(prev, depth)
        fmpz_one(prev + 0)
        fmpz_add(fmpz_mat_entry(U._matrix, r0, c0), fmpz_mat_entry(U._matrix, r0, c0), fk)
        # Row i (same recurrence as in moebius_moment_matrix), modulo p^(n - i)
        for i in range(1, min(depth, n)):
            fmpz_pow_ui(mi, fp, n - i)
            fmpz_mod(al, alpha, mi)
            fmpz_mod(be, beta, mi)
            fmpz_mod(ga, gamma, mi)
            fmpz_mul(tmp, be, prev + 0)
            fmpz_mod(cur + 0, tmp, mi)
            for j in range(1, depth):
                fmpz_mul(tmp, be, prev + j)
                fmpz_addmul(tmp, al, prev + j - 1)
                fmpz_addmul(tmp, ga, cur + j - 1)
                fmpz_mod(cur + j, tmp, mi)
            for j in range(depth):
                fmpz_addmul(fmpz_mat_entry(U._matrix, r0 + i, c0 + j), fk, cur + j)
            swap = prev
            prev = cur
            cur = swap
    finally:
        _fmpz_vec_clear(prev, depth)
        _fmpz_vec_clear(cur, depth)
        fmpz_clear(fp)
        fmpz_clear(fn)
        fmpz_clear(mi)
        fmpz_clear(dinv)
        fmpz_clear(alpha)
        fmpz_clear(beta)
        fmpz_clear(gamma)
        fmpz_clear(al)
        fmpz_clear(be)
        fmpz_clear(ga)
        fmpz_clear(tmp)
        fmpz_clear(fk)


cdef fmpz * _powers(fmpz_t p, slong n):
    r"""
    The vector ``(p^0, p^1, ..., p^n)`` (to be freed with ``_fmpz_vec_clear``).
    """
    cdef fmpz * pw = _fmpz_vec_init(n + 1)
    cdef slong k
    fmpz_one(pw + 0)
    for k in range(1, n + 1):
        fmpz_mul(pw + k, pw + k - 1, p)
    return pw


def moebius_moment_accumulate_scaled(Matrix_integer_dense U, slong r0, slong c0, coeff,
                                     a, b, c, d, p, slong n, slong depth):
    r"""
    Add ``coeff`` times the scaled moment matrix of ``[[a, b], [c, d]]`` to the
    ``depth`` by ``depth`` block of ``U`` starting at ``(r0, c0)``.

    Write the moment matrix of :func:`moebius_moment_matrix` as
    `y_i[j] = p^j z_i[j]`. If `d` is a unit and `c/d` and `(ad - bc)/d^2` are
    divisible by `p` (as for the products of a `U_p` representative and an
    element of `\Gamma_0(p)`), the entries `z_i[j]` are integral. Only the
    entries with `i + j < n` are computed, each modulo `p^{n - i - j}`, which is
    the precision of the filtration of overconvergent distributions (the
    moment `i` is meaningful modulo `p^{n - i}`). The entries of ``U`` are not
    reduced (see :func:`reduce_scaled_matrix`).

    It uses `r(z) = \beta + w z / (1 + e z)`, with `\beta = b/d`, `e = c/d` and
    `w = (ad - bc)/d^2`: then `y_i = \beta y_{i-1} + w u` with
    `(1 + e z) u = z y_{i-1}`, and with `u_j = p^{j-1} t_j`,

    .. MATH::

        t_j = z_{i-1}[j-1] - (e/p) t_{j-1}, \qquad z_i[j] = \beta z_{i-1}[j] + (w/p) t_j.

    Raise ``ValueError`` if `e` or `w` is not divisible by `p`.

    EXAMPLES::

        sage: from darmonpoints.moments import moebius_moment_matrix, moebius_moment_accumulate_scaled
        sage: p, n = 5, 6
        sage: a, b, c, d = 7, 3, 10, 2 * 5 + 1   # det = 7 * 11 - 30 = 47: not divisible by 5
        sage: U = matrix(ZZ, n + 1, n + 1)
        sage: moebius_moment_accumulate_scaled(U, 0, 0, 1, a, b, c, d, p, n, n + 1)
        Traceback (most recent call last):
        ...
        ValueError: the matrix does not satisfy the divisibility conditions
        sage: a, b, c, d = 5 * 7, 3, 10, 11      # det = 385 - 30 = 355 = 5 * 71
        sage: M = moebius_moment_matrix(a, b, c, d, p^n, n + 1)
        sage: moebius_moment_accumulate_scaled(U, 0, 0, 2, a, b, c, d, p, n, n + 1)
        sage: all((p^j * U[i, j] - 2 * M[i, j]) % p^(n - i) == 0
        ....:     for i in range(n) for j in range(n - i))
        True
    """
    cdef Integer P = Integer(p)
    cdef Integer K = Integer(coeff)
    cdef Integer A = Integer(a)
    cdef Integer B = Integer(b)
    cdef Integer C = Integer(c)
    cdef Integer D = Integer(d)
    cdef fmpz_t fp, fn, dinv, beta, e1, w1, tmp, fk, t, tprev
    cdef fmpz * pw
    cdef fmpz * prev
    cdef fmpz * cur
    cdef fmpz * swap
    cdef slong i, j, L
    if depth <= 0 or n <= 0:
        return
    if r0 < 0 or c0 < 0 or r0 + depth > U._nrows or c0 + depth > U._ncols:
        raise IndexError("block out of range")
    fmpz_init(fp)
    fmpz_init(fn)
    fmpz_init(dinv)
    fmpz_init(beta)
    fmpz_init(e1)
    fmpz_init(w1)
    fmpz_init(tmp)
    fmpz_init(fk)
    fmpz_init(t)
    fmpz_init(tprev)
    fmpz_set_mpz(fp, P.value)
    pw = _powers(fp, n)
    prev = _fmpz_vec_init(depth)
    cur = _fmpz_vec_init(depth)
    try:
        fmpz_set(fn, pw + n)
        fmpz_set_mpz(fk, K.value)
        fmpz_set_mpz(tmp, D.value)
        fmpz_mod(tmp, tmp, fn)
        if not fmpz_invmod(dinv, tmp, fn):
            raise ZeroDivisionError("d is not invertible modulo p^n")
        # beta = b/d, e = c/d, w = (ad - bc)/d^2 (mod p^n)
        fmpz_set_mpz(tmp, B.value)
        fmpz_mul(beta, tmp, dinv)
        fmpz_mod(beta, beta, fn)
        fmpz_set_mpz(tmp, C.value)
        fmpz_mul(e1, tmp, dinv)
        fmpz_mod(e1, e1, fn)
        fmpz_set_mpz(tmp, A.value)
        fmpz_set_mpz(w1, D.value)
        fmpz_mul(tmp, tmp, w1)
        fmpz_set_mpz(w1, B.value)
        fmpz_set_mpz(t, C.value)
        fmpz_submul(tmp, w1, t)
        fmpz_mul(tmp, tmp, dinv)
        fmpz_mul(tmp, tmp, dinv)
        fmpz_mod(w1, tmp, fn)
        if not (fmpz_divisible(e1, fp) and fmpz_divisible(w1, fp)):
            raise ValueError("the matrix does not satisfy the divisibility conditions")
        fmpz_divexact(e1, e1, fp)
        fmpz_divexact(w1, w1, fp)
        # Row 0: z_0 = (1, 0, ..., 0)
        _fmpz_vec_zero(prev, depth)
        fmpz_one(prev + 0)
        fmpz_add(fmpz_mat_entry(U._matrix, r0, c0), fmpz_mat_entry(U._matrix, r0, c0), fk)
        for i in range(1, n):
            L = n - i  # entries j < L, z_i[j] modulo p^(L - j)
            fmpz_mul(tmp, beta, prev + 0)
            fmpz_mod(cur + 0, tmp, pw + L)
            fmpz_zero(tprev)
            for j in range(1, L):
                # t_j = z_{i-1}[j-1] - e' t_{j-1}
                fmpz_set(t, prev + j - 1)
                fmpz_submul(t, e1, tprev)
                fmpz_mod(t, t, pw + L - j)
                # z_i[j] = beta z_{i-1}[j] + w' t_j
                fmpz_mul(tmp, beta, prev + j)
                fmpz_addmul(tmp, w1, t)
                fmpz_mod(cur + j, tmp, pw + L - j)
                fmpz_set(tprev, t)
            for j in range(L):
                fmpz_addmul(fmpz_mat_entry(U._matrix, r0 + i, c0 + j), fk, cur + j)
            # the entries of the previous row beyond L are not used any more
            swap = prev
            prev = cur
            cur = swap
    finally:
        _fmpz_vec_clear(prev, depth)
        _fmpz_vec_clear(cur, depth)
        _fmpz_vec_clear(pw, n + 1)
        fmpz_clear(fp)
        fmpz_clear(fn)
        fmpz_clear(dinv)
        fmpz_clear(beta)
        fmpz_clear(e1)
        fmpz_clear(w1)
        fmpz_clear(tmp)
        fmpz_clear(fk)
        fmpz_clear(t)
        fmpz_clear(tprev)


def reduce_scaled_matrix(Matrix_integer_dense U, p, slong n, slong depth):
    r"""
    Reduce, in place, the entry of ``U`` in row `m` and column `m'` of its
    ``depth`` by ``depth`` blocks modulo `p^{n - m - m'}` (to zero if
    `m + m' \geq n`), as produced by :func:`moebius_moment_accumulate_scaled`.

    EXAMPLES::

        sage: from darmonpoints.moments import reduce_scaled_matrix
        sage: U = matrix(ZZ, 4, 4, [10] * 16)
        sage: reduce_scaled_matrix(U, 3, 3, 2); U
        [10  1 10  1]
        [ 1  1  1  1]
        [10  1 10  1]
        [ 1  1  1  1]
    """
    cdef Integer P = Integer(p)
    cdef fmpz_t fp
    cdef fmpz * pw
    cdef slong r, c, k
    fmpz_init(fp)
    fmpz_set_mpz(fp, P.value)
    pw = _powers(fp, n)
    try:
        for r in range(U._nrows):
            for c in range(U._ncols):
                k = n - (r % depth) - (c % depth)
                if k <= 0:
                    fmpz_zero(fmpz_mat_entry(U._matrix, r, c))
                else:
                    fmpz_mod(fmpz_mat_entry(U._matrix, r, c), fmpz_mat_entry(U._matrix, r, c), pw + k)
    finally:
        _fmpz_vec_clear(pw, n + 1)
        fmpz_clear(fp)


def scaled_matvec(Matrix_integer_dense U, Matrix_integer_dense v, p, slong n, slong depth):
    r"""
    The product of the matrix `U \cdot \mathrm{diag}(p^{m'})` (``U`` scaled as
    in :func:`moebius_moment_accumulate_scaled`) and the column ``v``, with the
    entry in row `m` of each block reduced modulo `p^{n - m}`.

    Only the entries with `m + m' < n` of ``U`` are used, and the sum over `m'`
    is computed with Horner's rule in `p`.

    EXAMPLES::

        sage: from darmonpoints.moments import scaled_matvec
        sage: p, n, depth = 3, 3, 4
        sage: U = matrix(ZZ, 8, 8, lambda r, c: r + 2 * c + 1)
        sage: v = matrix(ZZ, 8, 1, list(range(1, 9)))
        sage: D = diagonal_matrix(ZZ, [p^(c % depth) for c in range(8)])
        sage: Z = matrix(ZZ, 8, 8, lambda r, c: U[r, c] if (r % depth) + (c % depth) < n else 0)
        sage: W = Z * D * v
        sage: w = scaled_matvec(U, v, p, n, depth)
        sage: all((w[r, 0] - W[r, 0]) % p^max(n - r % depth, 0) == 0 for r in range(8))
        True
        sage: all(0 <= w[r, 0] < p^max(n - r % depth, 0) or w[r, 0] == 0 for r in range(8))
        True
    """
    cdef Integer P = Integer(p)
    cdef fmpz_t fp, acc, s
    cdef fmpz * pw
    cdef slong r, m, mp, i, L, nblocks
    if U._ncols != v._nrows or v._ncols != 1 or U._ncols % depth != 0:
        raise ValueError("incompatible dimensions")
    nblocks = U._ncols // depth
    cdef Matrix_integer_dense w = MatrixSpace(ZZ, U._nrows, 1)()
    fmpz_init(fp)
    fmpz_init(acc)
    fmpz_init(s)
    fmpz_set_mpz(fp, P.value)
    pw = _powers(fp, n)
    try:
        for r in range(U._nrows):
            m = r % depth
            L = n - m
            if L <= 0:
                continue
            fmpz_zero(acc)
            for mp in range(L - 1, -1, -1):
                fmpz_mul(acc, acc, fp)
                for i in range(nblocks):
                    fmpz_addmul(acc, fmpz_mat_entry(U._matrix, r, i * depth + mp),
                                fmpz_mat_entry(v._matrix, i * depth + mp, 0))
            fmpz_mod(fmpz_mat_entry(w._matrix, r, 0), acc, pw + L)
    finally:
        _fmpz_vec_clear(pw, n + 1)
        fmpz_clear(fp)
        fmpz_clear(acc)
        fmpz_clear(s)
    return w


def filtration_valuation(Matrix_integer_dense v, p, slong n, slong depth):
    r"""
    Reduce, in place, the entry in row `m` of each block of the column ``v``
    modulo `p^{n - m}` (to zero if `m \geq n`), and return the smallest
    valuation of the nonzero entries (or `n` if they are all zero).

    EXAMPLES::

        sage: from darmonpoints.moments import filtration_valuation
        sage: v = matrix(ZZ, 6, 1, [9, 18, 4, 27, 54, 1])
        sage: filtration_valuation(v, 3, 3, 3), v.list()
        (0, [9, 0, 1, 0, 0, 1])
        sage: v = matrix(ZZ, 6, 1, [9, 18, 3, 27, 54, 0])
        sage: filtration_valuation(v, 3, 3, 3), v.list()
        (2, [9, 0, 0, 0, 0, 0])
        sage: v = matrix(ZZ, 3, 1, [27, 9, 3])
        sage: filtration_valuation(v, 3, 3, 3)
        3
    """
    cdef Integer P = Integer(p)
    cdef fmpz_t fp, q
    cdef fmpz * pw
    cdef slong r, m, k, val, best
    fmpz_init(fp)
    fmpz_init(q)
    fmpz_set_mpz(fp, P.value)
    pw = _powers(fp, n)
    best = n
    try:
        for r in range(v._nrows):
            m = r % depth
            if m >= n:
                fmpz_zero(fmpz_mat_entry(v._matrix, r, 0))
                continue
            fmpz_mod(fmpz_mat_entry(v._matrix, r, 0), fmpz_mat_entry(v._matrix, r, 0), pw + n - m)
            if fmpz_is_zero(fmpz_mat_entry(v._matrix, r, 0)):
                continue
            # valuation (at most best)
            val = 0
            while val < best and fmpz_divisible(fmpz_mat_entry(v._matrix, r, 0), pw + val + 1):
                val += 1
            if val < best:
                best = val
    finally:
        _fmpz_vec_clear(pw, n + 1)
        fmpz_clear(fp)
        fmpz_clear(q)
    return best


def divexact_inplace(Matrix_integer_dense v, q):
    r"""
    Divide, in place, all the entries of ``v`` by ``q`` (which must divide them).

    EXAMPLES::

        sage: from darmonpoints.moments import divexact_inplace
        sage: v = matrix(ZZ, 2, 1, [6, -9])
        sage: divexact_inplace(v, 3); v.list()
        [2, -3]
    """
    cdef Integer Q = Integer(q)
    cdef fmpz_t fq
    cdef slong r, c
    fmpz_init(fq)
    fmpz_set_mpz(fq, Q.value)
    try:
        for r in range(v._nrows):
            for c in range(v._ncols):
                fmpz_divexact(fmpz_mat_entry(v._matrix, r, c), fmpz_mat_entry(v._matrix, r, c), fq)
    finally:
        fmpz_clear(fq)


def add_block_scaled(Matrix_integer_dense U, slong r0, slong c0, coeff,
                     Matrix_integer_dense S, slong n, slong depth):
    r"""
    Add ``coeff`` times the entries `(i, j)` with `i + j < n` of the
    ``depth`` by ``depth`` matrix ``S`` to the block of ``U`` starting at
    ``(r0, c0)``.

    EXAMPLES::

        sage: from darmonpoints.moments import add_block_scaled
        sage: U = matrix(ZZ, 3, 3); S = matrix(ZZ, 2, 2, [1, 2, 3, 4])
        sage: add_block_scaled(U, 1, 0, 5, S, 2, 2); U
        [ 0  0  0]
        [ 5 10  0]
        [15  0  0]
    """
    cdef Integer K = Integer(coeff)
    cdef fmpz_t fk
    cdef slong i, j
    if r0 < 0 or c0 < 0 or r0 + depth > U._nrows or c0 + depth > U._ncols:
        raise IndexError("block out of range")
    if S._nrows < depth or S._ncols < depth:
        raise IndexError("S is too small")
    fmpz_init(fk)
    fmpz_set_mpz(fk, K.value)
    try:
        for i in range(min(depth, n)):
            for j in range(min(depth, n - i)):
                if not fmpz_is_zero(fmpz_mat_entry(S._matrix, i, j)):
                    fmpz_addmul(fmpz_mat_entry(U._matrix, r0 + i, c0 + j), fk,
                                fmpz_mat_entry(S._matrix, i, j))
    finally:
        fmpz_clear(fk)


def matrix_axpy(Matrix_integer_dense A, coeff, Matrix_integer_dense B):
    r"""
    ``A += coeff * B``, in place.

    EXAMPLES::

        sage: from darmonpoints.moments import matrix_axpy
        sage: A = matrix(ZZ, 2, 2, [1, 2, 3, 4]); B = matrix(ZZ, 2, 2, [1, 0, 0, 1])
        sage: matrix_axpy(A, -3, B); A
        [-2  2]
        [ 3  1]
    """
    cdef Integer K = Integer(coeff)
    cdef fmpz_t fk
    cdef slong i, j
    if A._nrows != B._nrows or A._ncols != B._ncols:
        raise ValueError("incompatible dimensions")
    fmpz_init(fk)
    fmpz_set_mpz(fk, K.value)
    try:
        for i in range(A._nrows):
            for j in range(A._ncols):
                fmpz_addmul(fmpz_mat_entry(A._matrix, i, j), fk, fmpz_mat_entry(B._matrix, i, j))
    finally:
        fmpz_clear(fk)


def filtration_weighted_valuation(Matrix_integer_dense v, p, slong n, slong depth):
    r"""
    The smallest value of `m + v_p(x)` over the nonzero entries `x` of the
    column ``v`` (in row `m` of its ``depth`` blocks), or `n` if there are none.

    For a column of scaled coefficients (the coefficient of degree `m` being
    `p^m x`), this is the valuation of the corresponding series.

    EXAMPLES::

        sage: from darmonpoints.moments import filtration_weighted_valuation
        sage: v = matrix(ZZ, 6, 1, [0, 9, 0, 0, 0, 3])
        sage: filtration_weighted_valuation(v, 3, 5, 3)
        3
    """
    cdef Integer P = Integer(p)
    cdef fmpz_t fp
    cdef fmpz * pw
    cdef slong r, m, val, best
    fmpz_init(fp)
    fmpz_set_mpz(fp, P.value)
    pw = _powers(fp, n)
    best = n
    try:
        for r in range(v._nrows):
            m = r % depth
            if m >= best or fmpz_is_zero(fmpz_mat_entry(v._matrix, r, 0)):
                continue
            val = 0
            while m + val < best and fmpz_divisible(fmpz_mat_entry(v._matrix, r, 0), pw + val + 1):
                val += 1
            if m + val < best:
                best = m + val
    finally:
        _fmpz_vec_clear(pw, n + 1)
        fmpz_clear(fp)
    return best


cdef class _OKArith:
    r"""
    Arithmetic modulo `N` in `\ZZ[g]/(g^2 - t_1 g - t_0)` (``d = 2``) or in
    `\ZZ` (``d = 1``), on pairs of ``fmpz``.
    """
    cdef fmpz_t N, t0, t1, s, u, v, w
    cdef slong d

    def __cinit__(self, N, t0, t1, slong d):
        fmpz_init(self.N); fmpz_init(self.t0); fmpz_init(self.t1)
        fmpz_init(self.s); fmpz_init(self.u); fmpz_init(self.v); fmpz_init(self.w)
        fmpz_set_mpz(self.N, (<Integer>Integer(N)).value)
        fmpz_set_mpz(self.t0, (<Integer>Integer(t0)).value)
        fmpz_set_mpz(self.t1, (<Integer>Integer(t1)).value)
        self.d = d

    def __dealloc__(self):
        fmpz_clear(self.N); fmpz_clear(self.t0); fmpz_clear(self.t1)
        fmpz_clear(self.s); fmpz_clear(self.u); fmpz_clear(self.v); fmpz_clear(self.w)

    cdef void mul(self, fmpz_t r0, fmpz_t r1, const fmpz_t a0, const fmpz_t a1,
                  const fmpz_t b0, const fmpz_t b1):
        # (a0 + a1 g)(b0 + b1 g), result may alias the inputs
        if self.d == 1:
            fmpz_mul(self.s, a0, b0)
            fmpz_mod(r0, self.s, self.N)
            fmpz_zero(r1)
            return
        fmpz_mul(self.w, a1, b1)
        fmpz_mul(self.s, a0, b0)
        fmpz_addmul(self.s, self.w, self.t0)
        fmpz_mul(self.u, a0, b1)
        fmpz_addmul(self.u, a1, b0)
        fmpz_addmul(self.u, self.w, self.t1)
        fmpz_mod(r0, self.s, self.N)
        fmpz_mod(r1, self.u, self.N)

    cdef int inv(self, fmpz_t r0, fmpz_t r1, const fmpz_t a0, const fmpz_t a1) except -1:
        # (a0 + a1 g)^-1 = (a0 + t1 a1 - a1 g) / (a0^2 + t1 a0 a1 - t0 a1^2)
        if self.d == 1:
            if not fmpz_invmod(r0, a0, self.N):
                raise ZeroDivisionError("not a unit")
            fmpz_zero(r1)
            return 0
        fmpz_mul(self.s, a0, a0)
        fmpz_mul(self.u, a0, a1)
        fmpz_addmul(self.s, self.u, self.t1)
        fmpz_mul(self.u, a1, a1)
        fmpz_submul(self.s, self.u, self.t0)
        fmpz_mod(self.s, self.s, self.N)
        if not fmpz_invmod(self.v, self.s, self.N):
            raise ZeroDivisionError("not a unit")
        fmpz_mul(self.u, a1, self.t1)
        fmpz_add(self.u, self.u, a0)
        fmpz_neg(self.w, a1)
        fmpz_mul(self.u, self.u, self.v)
        fmpz_mul(self.w, self.w, self.v)
        fmpz_mod(r0, self.u, self.N)
        fmpz_mod(r1, self.w, self.N)
        return 0


cdef _to_fmpz(fmpz_t r, x):
    fmpz_set_mpz(r, (<Integer>Integer(x)).value)


cdef _from_fmpz(const fmpz_t x):
    cdef Integer z = Integer(0)
    fmpz_get_mpz(z.value, x)
    return z


def mobius_transform_points(a, b, c, d, list xs, list ns, coeff, p, N, t0, t1, slong dK):
    r"""
    For the matrix `[[a, b], [c, d]]` (integers, `d` a unit modulo ``N``) and
    points `x_P` of `O = \ZZ[g]/(g^2 - t_1 g - t_0)` (``dK = 2``) or `\ZZ`
    (``dK = 1``), given by their coordinates ``xs`` modulo ``N`` and with
    multiplicities ``ns``, return the list of the coordinates of the points
    `(a x_P - c)/((d - b x_P) p)` (the numerators must be divisible by `p`),
    their weights ``coeff * n_P``, and the coordinates of
    `(\prod_P (1 - x_P b/d)^{n_P})^{coeff}`, all modulo ``N``.

    EXAMPLES::

        sage: from darmonpoints.moments import mobius_transform_points
        sage: N = 5^6
        sage: pts, ws, u = mobius_transform_points(2, 3, 5, 1, [[5], [10]], [1, -1], 2, 5, N, 0, 0, 1)
        sage: [((2 * x - 5) * pow(1 - 3 * x, -1, N) // 5) % N == y[0] for x, y in zip([5, 10], pts)] if False else ws
        [2, -2]
        sage: (pts[0][0] * 5 * (1 - 3 * 5) - (2 * 5 - 5)) % N
        0
        sage: (u[0] * (1 - 3 * 5)^-2 * (1 - 3 * 10)^2) % N == 1 if False else (u[0] * (1 - 3*10)^2 - (1 - 3*5)^2) % N
        0
    """
    cdef _OKArith A = _OKArith(N, t0, t1, dK)
    cdef fmpz_t fa, fb, fc, fd, fp, dinv, beta, x0, x1, y0, y1, q0, q1, u0, u1, e0, e1, tmp
    cdef slong k, j, nP, K
    fmpz_init(fa); fmpz_init(fb); fmpz_init(fc); fmpz_init(fd); fmpz_init(fp)
    fmpz_init(dinv); fmpz_init(beta); fmpz_init(x0); fmpz_init(x1)
    fmpz_init(y0); fmpz_init(y1); fmpz_init(q0); fmpz_init(q1)
    fmpz_init(u0); fmpz_init(u1); fmpz_init(e0); fmpz_init(e1); fmpz_init(tmp)
    points = []
    weights = []
    try:
        _to_fmpz(fa, a); _to_fmpz(fb, b); _to_fmpz(fc, c); _to_fmpz(fd, d); _to_fmpz(fp, p)
        fmpz_mod(fd, fd, A.N)
        if not fmpz_invmod(dinv, fd, A.N):
            raise ZeroDivisionError("d is not a unit")
        fmpz_mul(beta, fb, dinv)
        fmpz_mod(beta, beta, A.N)
        fmpz_one(u0); fmpz_zero(u1)
        for k in range(len(xs)):
            _to_fmpz(x0, xs[k][0])
            if dK == 2:
                _to_fmpz(x1, xs[k][1])
            else:
                fmpz_zero(x1)
            nP = ns[k]
            # e = 1 - x beta
            fmpz_mul(e0, x0, beta); fmpz_neg(e0, e0); fmpz_add_ui(e0, e0, 1); fmpz_mod(e0, e0, A.N)
            fmpz_mul(e1, x1, beta); fmpz_neg(e1, e1); fmpz_mod(e1, e1, A.N)
            if nP < 0:
                A.inv(e0, e1, e0, e1)
            for j in range(abs(nP)):
                A.mul(u0, u1, u0, u1, e0, e1)
            # q = (d - b x)^-1, y = (a x - c) q / p
            fmpz_mul(q0, fb, x0); fmpz_sub(q0, fd, q0); fmpz_mod(q0, q0, A.N)
            fmpz_mul(q1, fb, x1); fmpz_neg(q1, q1); fmpz_mod(q1, q1, A.N)
            A.inv(q0, q1, q0, q1)
            fmpz_mul(y0, fa, x0); fmpz_sub(y0, y0, fc); fmpz_mod(y0, y0, A.N)
            fmpz_mul(y1, fa, x1); fmpz_mod(y1, y1, A.N)
            A.mul(y0, y1, y0, y1, q0, q1)
            if not (fmpz_divisible(y0, fp) and fmpz_divisible(y1, fp)):
                raise ValueError("the transformed point is not in the maximal ideal")
            fmpz_divexact(y0, y0, fp)
            fmpz_divexact(y1, y1, fp)
            points.append([_from_fmpz(y0), _from_fmpz(y1)] if dK == 2 else [_from_fmpz(y0)])
            weights.append(Integer(coeff) * nP)
        # u^coeff
        K = coeff
        fmpz_set(e0, u0); fmpz_set(e1, u1)
        if K < 0:
            A.inv(e0, e1, e0, e1)
        fmpz_one(u0); fmpz_zero(u1)
        for j in range(abs(K)):
            A.mul(u0, u1, u0, u1, e0, e1)
        ucoords = [_from_fmpz(u0), _from_fmpz(u1)] if dK == 2 else [_from_fmpz(u0)]
        return points, weights, ucoords
    finally:
        fmpz_clear(fa); fmpz_clear(fb); fmpz_clear(fc); fmpz_clear(fd); fmpz_clear(fp)
        fmpz_clear(dinv); fmpz_clear(beta); fmpz_clear(x0); fmpz_clear(x1)
        fmpz_clear(y0); fmpz_clear(y1); fmpz_clear(q0); fmpz_clear(q1)
        fmpz_clear(u0); fmpz_clear(u1); fmpz_clear(e0); fmpz_clear(e1); fmpz_clear(tmp)


def chunk_fractions(list points, list weights, slong B, slong n, N, t0, t1, slong dK):
    r"""
    Split the points into chunks of ``B`` and return, for each chunk, the
    numerator and denominator of `\sum_k w_k / (1 - y_k T)`, truncated at
    `T^n`, as two lists of ``dK`` coefficient lists (modulo ``N``).

    EXAMPLES::

        sage: from darmonpoints.moments import chunk_fractions
        sage: R.<T> = ZZ[]
        sage: [(num, den)] = chunk_fractions([[2], [3]], [1, 5], 4, 4, 10^6, 0, 0, 1)
        sage: S = (R(num[0]) * R(den[0]).inverse_series_trunc(4)).truncate(4)
        sage: [c % 10^6 for c in S.list()] == [2^m + 5 * 3^m for m in range(4)]
        True
    """
    cdef _OKArith A = _OKArith(N, t0, t1, dK)
    cdef fmpz * n0 = _fmpz_vec_init(n + 1)
    cdef fmpz * n1 = _fmpz_vec_init(n + 1)
    cdef fmpz * d0 = _fmpz_vec_init(n + 1)
    cdef fmpz * d1 = _fmpz_vec_init(n + 1)
    cdef fmpz_t y0, y1, w, p0, p1, tmp0, tmp1
    cdef slong start, k, j, deg
    fmpz_init(y0); fmpz_init(y1); fmpz_init(w); fmpz_init(p0); fmpz_init(p1)
    fmpz_init(tmp0); fmpz_init(tmp1)
    ans = []
    try:
        for start in range(0, len(points), B):
            _fmpz_vec_zero(n0, n + 1); _fmpz_vec_zero(n1, n + 1)
            _fmpz_vec_zero(d0, n + 1); _fmpz_vec_zero(d1, n + 1)
            fmpz_one(d0 + 0)
            deg = 0
            for k in range(start, min(start + B, len(points))):
                _to_fmpz(y0, points[k][0])
                if dK == 2:
                    _to_fmpz(y1, points[k][1])
                else:
                    fmpz_zero(y1)
                _to_fmpz(w, weights[k])
                deg = min(deg + 1, n - 1)
                # num <- num (1 - y T) + w den ; den <- den (1 - y T), from the top
                for j in range(deg, -1, -1):
                    # new coefficient j: c_j - y c_{j-1} (for both), plus w den_j for num
                    fmpz_set(p0, n0 + j); fmpz_set(p1, n1 + j)
                    fmpz_addmul(p0, w, d0 + j); fmpz_addmul(p1, w, d1 + j)
                    if j > 0:
                        A.mul(tmp0, tmp1, n0 + j - 1, n1 + j - 1, y0, y1)
                        fmpz_sub(p0, p0, tmp0); fmpz_sub(p1, p1, tmp1)
                    fmpz_mod(n0 + j, p0, A.N); fmpz_mod(n1 + j, p1, A.N)
                    fmpz_set(p0, d0 + j); fmpz_set(p1, d1 + j)
                    if j > 0:
                        A.mul(tmp0, tmp1, d0 + j - 1, d1 + j - 1, y0, y1)
                        fmpz_sub(p0, p0, tmp0); fmpz_sub(p1, p1, tmp1)
                    fmpz_mod(d0 + j, p0, A.N); fmpz_mod(d1 + j, p1, A.N)
            num = [[_from_fmpz(n0 + j) for j in range(deg + 1)]]
            den = [[_from_fmpz(d0 + j) for j in range(deg + 1)]]
            if dK == 2:
                num.append([_from_fmpz(n1 + j) for j in range(deg + 1)])
                den.append([_from_fmpz(d1 + j) for j in range(deg + 1)])
            ans.append((num, den))
        return ans
    finally:
        _fmpz_vec_clear(n0, n + 1); _fmpz_vec_clear(n1, n + 1)
        _fmpz_vec_clear(d0, n + 1); _fmpz_vec_clear(d1, n + 1)
        fmpz_clear(y0); fmpz_clear(y1); fmpz_clear(w); fmpz_clear(p0); fmpz_clear(p1)
        fmpz_clear(tmp0); fmpz_clear(tmp1)
