# distutils: libraries = flint gmp
r"""
Fast computation of the matrices giving the action of `2 \times 2` matrices
on moments, as used by :class:`darmonpoints.ocmodule.OCVn`.
"""
from sage.libs.flint.types cimport fmpz_t, fmpz_poly_t, slong
from sage.libs.gmp.types cimport mpz_t

# Declared here rather than cimported from ``sage.libs.flint.fmpz``, whose
# ``.pxd`` is not usable in some Sage installations (it cimports a missing
# ``fmpz_macros.pxd``).
cdef extern from "flint_wrap.h":
    void fmpz_init(fmpz_t f) noexcept
    void fmpz_clear(fmpz_t f) noexcept
    void fmpz_set_mpz(fmpz_t f, const mpz_t x) noexcept
    void fmpz_set(fmpz_t f, const fmpz_t g) noexcept
    void fmpz_one(fmpz_t f) noexcept
    void fmpz_neg(fmpz_t f1, const fmpz_t f2) noexcept
    void fmpz_mul(fmpz_t f, const fmpz_t g, const fmpz_t h) noexcept
    void fmpz_addmul(fmpz_t f, const fmpz_t g, const fmpz_t h) noexcept
    void fmpz_mod(fmpz_t f, const fmpz_t g, const fmpz_t h) noexcept
    int fmpz_invmod(fmpz_t f, const fmpz_t g, const fmpz_t h) noexcept

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
