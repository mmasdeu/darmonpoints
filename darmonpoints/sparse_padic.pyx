# cython: boundscheck=False, wraparound=False, cdivision=True, language_level=3
r"""
Sparse integer matrices whose columns are only needed modulo powers of p.

This is the compiled kernel of ``meromorphic._IntegerOperator`` (mode
``'compiled'``), used for the iteration of Up in the additive Darmon-Vonk lift
(see ``LogSeriesOperator`` and ``OverconvergentDVCocycle._improve_integral``).
It computes ``v * A`` for row vectors ``v`` of integers, with column ``c`` reduced
modulo ``p^exps[c]``, exactly as the pure python products do, but:

- the entries are stored in a flat array of GMP limbs (no python object per
  entry), and the products are accumulated with ``mpz_addmul``;

- it takes advantage of the valuation of ``v``: if ``p^s`` divides every entry
  of ``v``, then ``(v * A)[c] mod p^e = p^s * ((v / p^s) * A[c] mod p^(e - s))``,
  so the entries of column ``c`` are only needed modulo ``p^(exps[c] - s)``. In
  the iteration of Up the valuation of ``v`` grows by about one at each step, so
  the products involve smaller and smaller numbers. Reduced copies of the
  matrix are built when ``s`` passes multiples of ``maxexp / levels`` (entries
  that vanish are dropped); only the latest one is kept, and the original
  entries are never modified (the matrix is shared, see
  ``OverconvergentDVCocycle.up_operator``, also by forked processes, which only
  read its memory).

EXAMPLES::

    sage: from darmonpoints.sparse_padic import SparsePadicMatrix
    sage: from array import array
    sage: p = 3
    sage: A = random_matrix(ZZ, 30, 20, x=0, y=3^40)
    sage: exps = [40] * 10 + [25] * 10
    sage: A = matrix(ZZ, 30, 20, lambda r, c: A[r, c] % 3^exps[c])
    sage: rows = [array('i', [r for r in range(30) if A[r, c]]) for c in range(20)]
    sage: vals = [[int(A[r, c]) for r in rows[c]] for c in range(20)]
    sage: S = SparsePadicMatrix(rows, vals, 30, exps, p)
    sage: S.nnz() == len(A.dict())
    True
    sage: ok = True
    sage: for s in [0, 1, 7, 20, 30, 39, 45]:
    ....:     v = [int(3^s * randrange(3^40)) for _ in range(30)]
    ....:     w = vector(ZZ, v) * A
    ....:     ok = ok and S.apply(v) == [int(w[c] % 3^exps[c]) for c in range(20)]
    sage: ok
    True
    sage: S.apply([0] * 30) == [0] * 20
    True
    sage: S.columns()[1] == vals
    True

Negative entries, and entries of any size (also those that fit in a machine
word), are converted exactly::

    sage: v = [int(randrange(-3^60, 3^60)) for _ in range(30)]
    sage: v[:3] = [-1, 2^63, -2^63 - 1]
    sage: w = vector(ZZ, v) * A
    sage: S.apply(v) == [int(w[c] % 3^exps[c]) for c in range(20)]
    True

The module only needs a C compiler and GMP (``gmp.h`` and ``libgmp``) to be
built, and not the Sage sources: it declares the few GMP functions that it
uses. If it is not built, the python products are used instead (see
``meromorphic._IntegerOperator``), with the same results.
"""
from cpython.bytes cimport PyBytes_AS_STRING, PyBytes_FromStringAndSize
from cpython.exc cimport PyErr_CheckSignals
from cpython.long cimport PyLong_AsLongAndOverflow, PyLong_FromLong
from libc.stdint cimport int32_t, int64_t
from libc.stdlib cimport free, malloc, realloc
from libc.string cimport memcpy, memset


cdef extern from "gmp.h":
    # The types and functions of GMP used here (the C types are those of gmp.h)
    ctypedef unsigned long mp_limb_t
    ctypedef long mp_size_t
    ctypedef unsigned long mp_bitcnt_t
    ctypedef struct __mpz_struct:
        int _mp_alloc
        int _mp_size
        mp_limb_t* _mp_d
    ctypedef __mpz_struct mpz_t[1]
    ctypedef __mpz_struct* mpz_ptr
    ctypedef const __mpz_struct* mpz_srcptr
    void mpz_init(mpz_ptr)
    void mpz_init2(mpz_ptr, mp_bitcnt_t)
    void mpz_init_set_ui(mpz_ptr, unsigned long)
    void mpz_clear(mpz_ptr)
    void mpz_set_ui(mpz_ptr, unsigned long)
    void mpz_set_si(mpz_ptr, long)
    long mpz_get_si(mpz_srcptr)
    int mpz_fits_slong_p(mpz_srcptr)
    void mpz_neg(mpz_ptr, mpz_srcptr)
    void mpz_mul(mpz_ptr, mpz_srcptr, mpz_srcptr)
    void mpz_addmul(mpz_ptr, mpz_srcptr, mpz_srcptr)
    void mpz_fdiv_r(mpz_ptr, mpz_srcptr, mpz_srcptr)
    void mpz_divexact(mpz_ptr, mpz_srcptr, mpz_srcptr)
    int mpz_divisible_p(mpz_srcptr, mpz_srcptr)
    int mpz_sgn(mpz_srcptr)
    size_t mpz_sizeinbase(mpz_srcptr, int)
    mpz_srcptr mpz_roinit_n(mpz_ptr, const mp_limb_t*, mp_size_t)
    void mpz_import(mpz_ptr, size_t, int, size_t, int, size_t, const void*)
    void* mpz_export(void*, size_t*, int, size_t, int, size_t, mpz_srcptr)


cdef int mpz_set_pylong(mpz_ptr z, x) except -1:
    # z = x, for a python integer x (through its bytes when it does not fit in a long)
    cdef int overflow = 0
    cdef long s = PyLong_AsLongAndOverflow(x, &overflow)
    if not overflow:
        mpz_set_si(z, s)
        return 0
    cdef bint negative = x < 0
    if negative:
        x = -x
    b = x.to_bytes((x.bit_length() + 7) // 8, 'little')
    mpz_import(z, len(b), -1, 1, 0, 0, PyBytes_AS_STRING(b))
    if negative:
        mpz_neg(z, z)
    return 0


cdef object mpz_get_pylong(mpz_srcptr z):
    # The python integer z (through its bytes when it does not fit in a long)
    if mpz_fits_slong_p(z):
        return PyLong_FromLong(mpz_get_si(z))
    cdef size_t n = (mpz_sizeinbase(z, 2) + 7) // 8  # exactly the bytes that mpz_export writes
    cdef size_t count = 0
    b = PyBytes_FromStringAndSize(NULL, n)  # filled before it is used anywhere
    mpz_export(PyBytes_AS_STRING(b), &count, -1, 1, 0, 0, z)
    x = int.from_bytes(b, 'little')
    return -x if mpz_sgn(z) < 0 else x


cdef inline int sig_check() except -1:
    # Let KeyboardInterrupt through (also under Sage, whose cysignals handler
    # sets the python interrupt flag outside sig_on blocks)
    return PyErr_CheckSignals()


cdef int LIMB_BITS = 8 * sizeof(mp_limb_t)


cdef struct Level:
    int shift             # the entries of column c are reduced modulo p^(exps[c] - shift)
    int nl                # limbs per entry
    int64_t nnz
    int64_t* starts       # ncols + 1
    int32_t* rows         # nnz
    mp_limb_t* limbs      # nnz * nl


cdef void free_level(Level* L) noexcept:
    free(L.starts)
    free(L.rows)
    free(L.limbs)
    L.starts = NULL
    L.rows = NULL
    L.limbs = NULL
    L.nnz = 0


cdef inline void store(mp_limb_t* dst, mpz_srcptr z, int nl) noexcept:
    # The limbs of the nonnegative integer z (with at most nl limbs), zero padded
    cdef int n = z._mp_size
    if n > 0:
        memcpy(dst, z._mp_d, n * sizeof(mp_limb_t))
    if n < nl:
        memset(dst + n, 0, (nl - n) * sizeof(mp_limb_t))


cdef class SparsePadicMatrix:
    r"""
    The matrix with ``nrows`` rows whose column ``c`` has nonzero entries
    ``vals[c]`` (python integers, reduced modulo ``p^exps[c]`` here) at the rows
    ``rows[c]``. See the module documentation.
    """
    cdef readonly long nrows, ncols
    cdef readonly int maxexp, levels
    cdef int* exps
    cdef __mpz_struct* ppow     # p^0, ..., p^maxexp
    cdef __mpz_struct* v        # the row vector of the product
    cdef __mpz_struct tmp, acc, ro
    cdef Level base             # the original entries
    cdef Level cur              # the current reduced copy (shift > 0), or none (starts == NULL)
    cdef object p

    def __cinit__(self):
        self.exps = NULL
        self.ppow = NULL
        self.v = NULL
        self.base.starts = NULL
        self.base.rows = NULL
        self.base.limbs = NULL
        self.cur.starts = NULL
        self.cur.rows = NULL
        self.cur.limbs = NULL
        self.nrows = 0
        self.maxexp = -1
        mpz_init(&self.tmp)
        mpz_init(&self.acc)

    def __init__(self, rows, vals, long nrows, exps, p, int levels=8):
        cdef long c, r, k, j
        cdef int64_t nnz = 0
        self.p = int(p)
        self.ncols = len(exps)
        self.nrows = nrows
        self.levels = max(1, levels)
        if len(rows) != self.ncols or len(vals) != self.ncols:
            raise ValueError("rows and vals must have one entry per column")
        self.exps = <int*> malloc(max(1, self.ncols) * sizeof(int))
        self.maxexp = 0
        for c in range(self.ncols):
            self.exps[c] = max(0, int(exps[c]))
            self.maxexp = max(self.maxexp, self.exps[c])
        self.ppow = <__mpz_struct*> malloc((self.maxexp + 1) * sizeof(__mpz_struct))
        mpz_init_set_ui(&self.ppow[0], 1)
        cdef mpz_t P
        mpz_init(P)
        mpz_set_pylong(P, self.p)
        for k in range(1, self.maxexp + 1):
            mpz_init(&self.ppow[k])
            mpz_mul(&self.ppow[k], &self.ppow[k - 1], P)
        mpz_clear(P)
        self.v = <__mpz_struct*> malloc(max(1, nrows) * sizeof(__mpz_struct))
        for r in range(nrows):
            mpz_init(&self.v[r])
        cdef size_t bits = mpz_sizeinbase(&self.ppow[self.maxexp], 2)
        mpz_init2(&self.acc, 2 * bits + 64)
        # The original entries
        for c in range(self.ncols):
            if len(rows[c]) != len(vals[c]):
                raise ValueError(f"column {c}: {len(rows[c])} rows and {len(vals[c])} values")
            nnz += len(rows[c])
        cdef Level* B = &self.base
        B.shift = 0
        B.nl = max(1, <int>((bits + LIMB_BITS - 1) // LIMB_BITS))
        B.starts = <int64_t*> malloc((self.ncols + 1) * sizeof(int64_t))
        B.rows = <int32_t*> malloc(max(1, nnz) * sizeof(int32_t))
        B.limbs = <mp_limb_t*> malloc(max(1, nnz) * B.nl * sizeof(mp_limb_t))
        if B.starts == NULL or B.rows == NULL or B.limbs == NULL:
            raise MemoryError
        k = 0
        for c in range(self.ncols):
            B.starts[c] = k
            for r, a in zip(rows[c], vals[c]):
                if r < 0 or r >= nrows:
                    raise ValueError(f"row {r} out of range in column {c}")
                mpz_set_pylong(&self.tmp, int(a))
                mpz_fdiv_r(&self.tmp, &self.tmp, &self.ppow[self.exps[c]])
                if mpz_sgn(&self.tmp) == 0:
                    continue
                B.rows[k] = r
                store(B.limbs + k * B.nl, &self.tmp, B.nl)
                k += 1
        B.starts[self.ncols] = k
        B.nnz = k

    def __dealloc__(self):
        cdef long k
        free_level(&self.base)
        free_level(&self.cur)
        if self.ppow != NULL:
            for k in range(self.maxexp + 1):
                mpz_clear(&self.ppow[k])
            free(self.ppow)
        if self.v != NULL:
            for k in range(self.nrows):
                mpz_clear(&self.v[k])
            free(self.v)
        free(self.exps)
        mpz_clear(&self.tmp)
        mpz_clear(&self.acc)

    def nnz(self):
        r"""
        The number of nonzero (original) entries.
        """
        return self.base.nnz

    def nbytes(self):
        r"""
        The memory used by the original entries and by the current reduced copy
        (for diagnostics).
        """
        ans = 0
        if self.base.starts != NULL:
            ans += (self.ncols + 1) * 8 + self.base.nnz * (4 + sizeof(mp_limb_t) * self.base.nl)
        if self.cur.starts != NULL:
            ans += (self.ncols + 1) * 8 + self.cur.nnz * (4 + sizeof(mp_limb_t) * self.cur.nl)
        return ans

    def columns(self):
        r"""
        The pair (rows, vals) of lists of the original entries, by columns.
        """
        from array import array
        cdef long c, k
        cdef Level* B = &self.base
        rows, vals = [], []
        for c in range(self.ncols):
            rows.append(array('i', [B.rows[k] for k in range(B.starts[c], B.starts[c + 1])]))
            vc = []
            for k in range(B.starts[c], B.starts[c + 1]):
                mpz_roinit_n(&self.ro, B.limbs + k * B.nl, B.nl)
                vc.append(mpz_get_pylong(&self.ro))
            vals.append(vc)
        return rows, vals

    cdef Level* _level(self, int s) except NULL:
        # The copy of the matrix to use when p^s divides v: one with shift <= s
        cdef int step = max(1, (self.maxexp + self.levels - 1) // self.levels)
        cdef int target = (s // step) * step
        if target > self.maxexp:
            target = self.maxexp
        if self.cur.starts != NULL:
            if self.cur.shift == target:
                return &self.cur
            if self.cur.shift > target:
                free_level(&self.cur)  # a new product (or a smaller valuation): start again
        if target == 0:
            return &self.base
        cdef Level* src = &self.cur if self.cur.starts != NULL else &self.base
        if target - src.shift < step:
            return src
        # Reduce src modulo p^(exps[c] - target), dropping the entries that vanish
        cdef Level L
        cdef size_t bits = mpz_sizeinbase(&self.ppow[max(0, self.maxexp - target)], 2)
        L.shift = target
        L.nl = max(1, <int>((bits + LIMB_BITS - 1) // LIMB_BITS))
        L.starts = <int64_t*> malloc((self.ncols + 1) * sizeof(int64_t))
        L.rows = <int32_t*> malloc(max(1, src.nnz) * sizeof(int32_t))
        L.limbs = <mp_limb_t*> malloc(max(1, src.nnz) * L.nl * sizeof(mp_limb_t))
        if L.starts == NULL or L.rows == NULL or L.limbs == NULL:
            free_level(&L)
            raise MemoryError
        cdef long c
        cdef int64_t k, n = 0
        cdef int e
        for c in range(self.ncols):
            sig_check()
            L.starts[c] = n
            e = self.exps[c] - target
            if e <= 0:
                continue
            for k in range(src.starts[c], src.starts[c + 1]):
                mpz_roinit_n(&self.ro, src.limbs + k * src.nl, src.nl)
                mpz_fdiv_r(&self.tmp, &self.ro, &self.ppow[e])
                if mpz_sgn(&self.tmp) == 0:
                    continue
                L.rows[n] = src.rows[k]
                store(L.limbs + n * L.nl, &self.tmp, L.nl)
                n += 1
        L.starts[self.ncols] = n
        L.nnz = n
        if n > 0:
            L.rows = <int32_t*> realloc(L.rows, n * sizeof(int32_t))
            L.limbs = <mp_limb_t*> realloc(L.limbs, n * L.nl * sizeof(mp_limb_t))
        if self.cur.starts != NULL:
            free_level(&self.cur)
        self.cur = L
        return &self.cur

    def reset(self):
        r"""
        Free the reduced copy of the matrix (to release memory between
        computations; it is rebuilt when needed).
        """
        free_level(&self.cur)

    def apply(self, list v):
        r"""
        The list of the entries ``(v * A)[c] mod p^exps[c]`` (python integers in
        ``[0, p^exps[c])``), for a list ``v`` of ``nrows`` integers.
        """
        cdef long r, c
        cdef int64_t k
        cdef int s, e, lo, hi, mid
        if len(v) != self.nrows:
            raise ValueError(f"the vector must have {self.nrows} entries")
        for r in range(self.nrows):
            x = v[r]
            if type(x) is not int:
                x = int(x)
            mpz_set_pylong(&self.v[r], x)
        # s = min of the valuations of the entries of v (at most maxexp)
        s = self.maxexp
        for r in range(self.nrows):
            if s == 0:
                break
            if mpz_sgn(&self.v[r]) == 0 or mpz_divisible_p(&self.v[r], &self.ppow[s]):
                continue
            # The valuation of v[r] is in [lo, s)
            lo, hi = 0, s - 1
            while lo < hi:
                mid = (lo + hi + 1) // 2
                if mpz_divisible_p(&self.v[r], &self.ppow[mid]):
                    lo = mid
                else:
                    hi = mid - 1
            s = lo
        if s > 0:
            for r in range(self.nrows):
                mpz_divexact(&self.v[r], &self.v[r], &self.ppow[s])
        cdef Level* L = self._level(s)
        ans = [0] * self.ncols
        for c in range(self.ncols):
            sig_check()
            e = self.exps[c] - s
            if e <= 0:
                continue
            mpz_set_ui(&self.acc, 0)
            for k in range(L.starts[c], L.starts[c + 1]):
                mpz_roinit_n(&self.ro, L.limbs + k * L.nl, L.nl)
                mpz_addmul(&self.acc, &self.v[L.rows[k]], &self.ro)
            mpz_fdiv_r(&self.acc, &self.acc, &self.ppow[e])
            if s > 0:
                mpz_mul(&self.acc, &self.acc, &self.ppow[s])
            if mpz_sgn(&self.acc) != 0:
                ans[c] = mpz_get_pylong(&self.acc)
        return ans


def propagate_precisions(const int32_t[::1] src, const int32_t[::1] mval, const int32_t[::1] mprec,
                         const int64_t[::1] targets, const int64_t[::1] starts,
                         const int64_t[::1] precs, const int64_t[::1] vals, int64_t[::1] out):
    r"""
    The precision propagation of ``LogSeriesOperator.propagate``: for each
    target ``t = targets[i]``, whose entries are ``starts[i] <= e < starts[i + 1]``
    (or the end of the arrays), set ``out[t]`` to the minimum of ``out[t]`` and of
    ``min(precs[src[e]] + mval[e], mprec[e] + vals[src[e]])``.

    EXAMPLES::

        sage: import numpy as np
        sage: from darmonpoints.sparse_padic import propagate_precisions
        sage: src = np.array([0, 1, 1, 2], dtype=np.int32)
        sage: mval = np.array([1, 0, 2, 0], dtype=np.int32)
        sage: mprec = np.array([10, 10, 3, 10], dtype=np.int32)
        sage: targets = np.array([0, 2], dtype=np.int64); starts = np.array([0, 2], dtype=np.int64)
        sage: precs = np.array([5, 7, 9], dtype=np.int64); vals = np.array([0, 1, 0], dtype=np.int64)
        sage: out = np.full(3, 10, dtype=np.int64)
        sage: propagate_precisions(src, mval, mprec, targets, starts, precs, vals, out)
        sage: list(out)
        [6, 10, 4]
    """
    cdef Py_ssize_t i, e, end, n = targets.shape[0], m = src.shape[0]
    cdef int64_t best, q, q2
    cdef int32_t r
    with nogil:
        for i in range(n):
            end = starts[i + 1] if i + 1 < n else m
            best = out[targets[i]]
            for e in range(starts[i], end):
                r = src[e]
                q = precs[r] + mval[e]
                q2 = mprec[e] + vals[r]
                if q2 < q:
                    q = q2
                if q < best:
                    best = q
            out[targets[i]] = best
