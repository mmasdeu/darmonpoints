r"""
CHANGED VERSION AS OF 31/10/2019.

We have gutted Maite Aranes' original code to look for hacks to speed it up;
in particular we have removed the functionality of MSymbol, almost all the check,
and replaced in-built functions (such as is_coprime) with hacked, but faster,
global functions (e.g. new_is_coprime).

The new functions should plug in as before. Instead of MSymbol we now use
MyMSymbol, which does much less.

To speed up: normalize_tuple, the global function, still uses lots of in-built
ideal functionality which should be replaced by more hacky global functions in
this file.

lift_to_sl2_Ok is also unchanged: may be speed ups here (though we don't call it
that many times in the main code).

Replacements over Maite's code:

    - replaced p1NFlist with my_p1NFlist
    - replaced MSymbol with MyMSymbol
    - replaced some in-built ideal functionality
    - REMOVED ALL CHECK!!!

"""

from sage.misc.search import search
from sage.structure.richcmp import richcmp, richcmp_method
from sage.structure.sage_object import SageObject

_level_cache = {}  # The info stored here is used in the normalization.


def P1NFList_clear_level_cache():
    """
    Clear the global cache of data for the level ideals.
    """
    global _level_cache
    _level_cache = {}


# **************************************************************************
# *       P1NFList class                                                   *
# **************************************************************************


class MyMSymbol(SageObject):
    """
    Dummy class for representing tuples with tuples.

    Gutted the previous MSymbol class to just essentially work with tuples.
    However, still wanted MSymbol.tuple() to work for compatibility with our
    other code.
    """

    def __init__(self, c, d):
        self._c = c
        self._d = d

    def __repr__(self):
        return "{}".format(self.tuple())

    def tuple(self):
        return (self._c, self._d)


@richcmp_method
class P1NFList(SageObject):
    r"""
    The class for `\mathbb{P}^1(R/N)`, the projective line modulo `N`, where
    `R` is the ring of integers of a number field `K` and `N` is an integral ideal.

    INPUT:

    -  ``N`` - integral ideal (the modulus or level).

    OUTPUT:

    A P1NFList object representing `\mathbb{P}^1(R/N)`.

    EXAMPLES::

        sage: k.<a> = NumberField(x^3 + 11)
        sage: N = k.ideal(5, a + 1)
        sage: P = P1NFList(N); P
        The projective line over the ring of integers modulo the Fractional ideal (5, a + 1)
    """

    def __init__(self, N):
        """
        The constructor for the class P1NFList. See ``P1NFList`` for full
        documentation.

        EXAMPLES::

            sage: k.<a> = NumberField(x^2 + 5)
            sage: N = k.ideal(3, a - 1)
            sage: P = P1NFList(N); P
            The projective line over the ring of integers modulo the Fractional ideal (3, a + 2)
        """
        self.__N = N
        self.__list = my_p1NFlist(N)
        # self.__list.sort()

    def __richcmp__(self, other, op):
        """
        Comparison function for objects of the class P1NFList.

        The order is the same as for the underlying modulus.

        EXAMPLES::

            sage: k.<a> = NumberField(x^2 + 23)
            sage: N1 = k.ideal(3, a + 1)
            sage: P1 = P1NFList(N1)
            sage: N2 = k.ideal(a + 2)
            sage: P2 = P1NFList(N2)
            sage: P1 < P2
            True
            sage: P1 > P2
            False
            sage: P1 == P1NFList(N1)
            True
        """
        if not isinstance(other, P1NFList):
            raise ValueError("You can only compare with another P1NFList")
        return richcmp(self.__N, other.__N, op)

    def __getitem__(self, n):
        """
        Standard indexing function for the class P1NFList.

        EXAMPLES::

            sage: k.<a> = NumberField(x^3 + 11)
            sage: N = k.ideal(a)
            sage: P = P1NFList(N)
            sage: list(P) == P._P1NFList__list
            True
            sage: j = randint(0,len(P)-1)
            sage: P[j] == P._P1NFList__list[j]
            True
        """
        return self.__list[n]

    def __len__(self):
        """
        Returns the length of this P1NFList.

        EXAMPLES::

            sage: k.<a> = NumberField(x^3 + 11)
            sage: N = k.ideal(5, a^2 - a + 1)
            sage: P = P1NFList(N)
            sage: len(P)
            26
        """
        return len(self.__list)

    def __repr__(self):
        """
        Returns the string representation of this P1NFList.

        EXAMPLES::

            sage: k.<a> = NumberField(x^3 + 11)
            sage: N = k.ideal(5, a+1)
            sage: P = P1NFList(N); P
            The projective line over the ring of integers modulo the Fractional ideal (5, a + 1)

        """
        return "The projective line over the ring of integers modulo the %s" % self.__N

    def list(self):
        """
        Returns the underlying list of this P1NFList object.

        EXAMPLES::

            sage: k.<a> = NumberField(x^3 + 11)
            sage: N = k.ideal(5, a+1)
            sage: P = P1NFList(N)
            sage: type(P)
            <class 'sage.modular.modsym.p1list_nf.P1NFList'>
            sage: type(P.list())
            <... 'list'>
        """
        return self.__list

    def normalize(self, c, d, with_scalar=False):
        r"""
        [We have gutted this function from its orginal state!]
        [Note: there is now no check!]

        Return a normalized  element of (a canonical representative of an element
        of `\mathbb{P}^1(R/N)` ) equivalent to ``elt``.

        INPUT:

        - ``c``,``d`` -- corr. to the tuple (c,d) that we wish to normalize
        - ``with_scalar`` -- bool (default False)

        OUTPUT:

        - (only if ``with_scalar=True``) a transforming scalar `u`, such that
          `(u*c', u*d')` is congruent to `(c: d)` (mod `N`), where `(c: d)`
          are the coefficients of ``self`` and `N` is the level.

        -  a normalized tuple (c', d') equivalent to ``self`` in P^1(R/N).

        """
        return normalize_tuple(self.__N, (c, d), with_scalar)

    def N(self):
        """
        Returns the level or modulus of this P1NFList.

        EXAMPLES::

            sage: k.<a> = NumberField(x^2 + 31)
            sage: N = k.ideal(5, a + 3)
            sage: P = P1NFList(N)
            sage: P.N()
            Fractional ideal (5, 1/2*a + 3/2)
        """
        return self.__N

    def lift_to_sl2_Ok(self, i):
        """
        Lift the `i`-th element of this P1NFList to an element of `SL(2, R)`,
        where `R` is the ring of integers of the corresponding number field.

        INPUT:

        - ``i`` - integer (index of the element to lift)

        OUTPUT:

        If the `i`-th element is `(c : d)`, the function returns a list of
        integral elements `[a, b, c', d']` that defines a 2x2 matrix with
        determinant 1 and such that `c=c'` (mod `N`) and `d=d'` (mod `N`).

        EXAMPLES::

            sage: k.<a> = NumberField(x^2 + 23)
            sage: N = k.ideal(3)
            sage: P = P1NFList(N)
            sage: len(P)
            16
            sage: P[5]
            M-symbol (1/2*a + 1/2: -a) of level Fractional ideal (3)
            sage: P.lift_to_sl2_Ok(5)
            [-a, 2*a - 2, 1/2*a + 1/2, -a]

        ::

            sage: Ok = k.ring_of_integers()
            sage: L = [Matrix(Ok, 2, P.lift_to_sl2_Ok(i)) for i in range(len(P))]
            sage: all(det(L[i]) == 1 for i in range(len(L)))
            True
        """
        return self[i].lift_to_sl2_Ok()

    def apply_S(self, i):
        """
        Applies the matrix S = [0, -1, 1, 0] to the i-th M-Symbol of the list.

        INPUT:

        - ``i`` -- integer

        OUTPUT:

        integer -- the index of the M-Symbol obtained by the right action of
        the matrix S = [0, -1, 1, 0] on the i-th M-Symbol.

        EXAMPLES::

            sage: k.<a> = NumberField(x^3 + 11)
            sage: N = k.ideal(5, a + 1)
            sage: P = P1NFList(N)
            sage: j = P.apply_S(P.index_of_normalized_pair(1, 0))
            sage: P[j]
            M-symbol (0: 1) of level Fractional ideal (5, a + 1)

        We test that S has order 2:

        ::

            sage: j = randint(0,len(P)-1)
            sage: P.apply_S(P.apply_S(j))==j
            True
        """
        c, d = self.__list[i].tuple()
        t, j = search(self.__list, self.normalize(d, -c))
        return j

    def apply_TS(self, i):
        """
        Applies the matrix TS = [1, -1, 0, 1] to the i-th M-Symbol of the list.

        INPUT:

        - ``i`` -- integer

        OUTPUT:

        integer -- the index of the M-Symbol obtained by the right action of
        the matrix TS = [1, -1, 0, 1] on the i-th M-Symbol.

        EXAMPLES::

            sage: k.<a> = NumberField(x^3 + 11)
            sage: N = k.ideal(5, a + 1)
            sage: P = P1NFList(N)
            sage: P.apply_TS(3)
            2

        We test that TS has order 3:

        ::

            sage: j = randint(0,len(P)-1)
            sage: P.apply_TS(P.apply_TS(P.apply_TS(j)))==j
            True
        """
        c, d = self.__list[i].tuple()
        t, j = search(self.__list, self.normalize(c + d, -c))
        return j

    def apply_T_alpha(self, i, alpha=1):
        """
        Applies the matrix T_alpha = [1, alpha, 0, 1] to the i-th M-Symbol of
        the list.

        INPUT:

        - ``i`` -- integer

        - ``alpha`` -- element of the corresponding ring of integers(default 1)

        OUTPUT:

        integer -- the index of the M-Symbol obtained by the right action of
        the matrix T_alpha = [1, alpha, 0, 1] on the i-th M-Symbol.

        EXAMPLES::

            sage: k.<a> = NumberField(x^3 + 11)
            sage: N = k.ideal(5, a + 1)
            sage: P = P1NFList(N)
            sage: P.apply_T_alpha(4, a^ 2 - 2)
            3

        We test that T_a*T_b = T_(a+b):

        ::

            sage: P.apply_T_alpha(3, a^2 - 2)==P.apply_T_alpha(P.apply_T_alpha(3,a^2),-2)
            True
        """
        c, d = self.__list[i].tuple()
        t, j = search(self.__list, self.normalize(c, alpha * c + d))
        return j

    def apply_J_epsilon(self, i, e1, e2=1):
        r"""
        Apply the matrix `J_{\epsilon}` = [e1, 0, 0, e2] to the i-th
        M-Symbol of the list.

        e1, e2 are units of the underlying number field.

        INPUT:

        - ``i`` -- integer

        - ``e1`` -- unit

        - ``e2`` -- unit (default 1)

        OUTPUT:

        integer -- the index of the M-Symbol obtained by the right action of
        the matrix `J_{\epsilon}` = [e1, 0, 0, e2] on the i-th M-Symbol.

        EXAMPLES::

            sage: k.<a> = NumberField(x^3 + 11)
            sage: N = k.ideal(5, a + 1)
            sage: P = P1NFList(N)
            sage: u = k.unit_group().gens_values()
            sage: len(u)
            2
            sage: P.apply_J_epsilon(4, -1)
            2
            sage: P.apply_J_epsilon(4, u[0], u[1])
            5

        ::

            sage: k.<a> = NumberField(x^4 + 13*x - 7)
            sage: N = k.ideal(a + 1)
            sage: P = P1NFList(N)
            sage: u = k.unit_group().gens_values()
            sage: len(u)
            3
            sage: P.apply_J_epsilon(3, u[2]^2)==P.apply_J_epsilon(P.apply_J_epsilon(3, u[2]),u[2])
            True
        """
        c, d = self.__list[i].tuple()
        t, j = search(self.__list, self.normalize(c * e1, d * e2))
        return j


# **************************************************************************
#  Global functions:
#    - p1NFList --compute list of M-symbols
#    - lift_to_sl2_Ok
#    - make_coprime -- need it for ``lift_to_sl2_Ok``
#    - psi -- useful to check cardinality of the M-symbols list
# **************************************************************************


def my_p1NFlist(N):
    """
    New hacked version of in-built sage function p1NFlist.
        - instead of MSymbol, uses MyMSymbol
        - instead of MSymbol's normalize, uses hacked global function normalize_tuple
        - removed all check

    Previous documentation:

    Returns a list of the normalized elements of `\\mathbb{P}^1(R/N)`, where
    `N` is an integral ideal.

    INPUT:

    -  ``N`` - integral ideal (the level or modulus).

    EXAMPLES::

        sage: k.<a> = NumberField(x^2 + 23)
        sage: N = k.ideal(3)
        sage: from sage.modular.modsym.p1list_nf import p1NFlist, psi
        sage: len(p1NFlist(N))==psi(N)
        True
    """
    k = N.number_field()

    L = [MyMSymbol(0, 1)]
    # N.residues() = iterator through the residues mod N
    L = L + [MyMSymbol(k(1), r) for r in N.residues()]

    from sage.arith.all import divisors

    for D in divisors(N):
        if not D.is_trivial() and D != N:
            # we find Dp ideal coprime to N, in inverse class to D

            Dp = k.ideal(1)
            c = D.gens_reduced()[0]

            # now we find all the (c,d)'s which have associated divisor D
            J = N / D
            I = D + J
            for d in J.residues():
                if new_is_coprime(I, k.ideal(d)):
                    M = D.prime_to_idealM_part(J)
                    u = (Dp * M).element_1_mod(J)
                    d1 = u * d + (1 - u)
                    L.append(normalize_tuple(N, (c, d1)))
    return L


def lift_to_sl2_Ok(N, c, d):
    """
    Lift a pair (c, d) to an element of `SL(2, O_k)`, where `O_k` is the ring
    of integers of the corresponding number field.

    INPUT:

    - ``N`` -- number field ideal

    - ``c`` -- integral element of the number field

    - ``d`` -- integral element of the number field

    OUTPUT:

    A list [a, b, c', d'] of integral elements that are the entries of
    a 2x2 matrix with determinant 1. The lower two entries are congruent to
    c, d modulo the ideal `N`.


    EXAMPLES::

        sage: from sage.modular.modsym.p1list_nf import lift_to_sl2_Ok
        sage: k.<a> = NumberField(x^2 + 23)
        sage: Ok = k.ring_of_integers()
        sage: N = k.ideal(3)
        sage: M = Matrix(Ok, 2, lift_to_sl2_Ok(N, 1, a))
        sage: det(M)
        1
        sage: M = Matrix(Ok, 2, lift_to_sl2_Ok(N, 0, a))
        sage: det(M)
        1
        sage: (M[1][0] in N) and (M[1][1] - a in N)
        True
        sage: M = Matrix(Ok, 2, lift_to_sl2_Ok(N, 0, 0))
        Traceback (most recent call last):
        ...
        ValueError: Cannot lift (0, 0) to an element of Sl2(Ok).

    ::

        sage: k.<a> = NumberField(x^3 + 11)
        sage: Ok = k.ring_of_integers()
        sage: N = k.ideal(3, a - 1)
        sage: M = Matrix(Ok, 2, lift_to_sl2_Ok(N, 2*a, 0))
        sage: det(M)
        1
        sage: (M[1][0] - 2*a in N) and (M[1][1] in N)
        True
        sage: M = Matrix(Ok, 2, lift_to_sl2_Ok(N, 4*a^2, a + 1))
        sage: det(M)
        1
        sage: (M[1][0] - 4*a^2 in N) and (M[1][1] - (a+1) in N)
        True

    ::

        sage: k.<a> = NumberField(x^4 - x^3 -21*x^2 + 17*x + 133)
        sage: Ok = k.ring_of_integers()
        sage: N = k.ideal(7, a)
        sage: M = Matrix(Ok, 2, lift_to_sl2_Ok(N, 0, a^2 - 1))
        sage: det(M)
        1
        sage: (M[1][0] in N) and (M[1][1] - (a^2-1) in N)
        True
        sage: M = Matrix(Ok, 2, lift_to_sl2_Ok(N, 0, 7))
        Traceback (most recent call last):
        ...
        ValueError: <0> + <7> and the Fractional ideal (7, a) are not coprime.
    """
    k = N.number_field()
    if type(c) is int:
        c = k(c)
    if type(d) is int:
        d = k(d)

    # check the input
    if c == 0 and d == 0:
        raise ValueError("Cannot lift (%s, %s) to an element of Sl2(Ok)." % (c, d))
    if not new_is_coprime(N, k.ideal(c, d)):
        raise ValueError("<%s> + <%s> and the %s are not coprime." % (c, d, N))
    # a few special cases
    if (c - 1).mod(N) == 0:
        return [k(0), k(-1), 1, d]
    if (d - 1).mod(N) == 0:
        return [k(1), k(0), c, 1]
    if c == 0:  # and d!=1, so won't happen for normalized M-symbols (c: d)
        it = k.primes_of_degree_one_iter()
        q = k.ideal(1)
        while not (new_is_coprime(q, d) and (q * N).is_principal()):
            q = next(it)
        m = (q * N).gens_reduced()[0]
        B = k.ideal(m).element_1_mod(k.ideal(d))
        return [(1 - B) / d, -B / m, m, d]
    if d == 0:  # and c!=1, so won't happen for normalized M-symbols (c: d)
        it = k.primes_of_degree_one_iter()
        q = k.ideal(1)
        while not (new_is_coprime(q, c) and (q * N).is_principal()):
            q = next(it)
        m = (q * N).gens_reduced()[0]
        B = k.ideal(c).element_1_mod(k.ideal(m))
        return [(1 - B) / m, -B / c, c, m]

    c, d = make_coprime(N, c, d)

    B = k.ideal(c).element_1_mod(k.ideal(d))
    b = -B / c
    a = (1 - B) / d
    return [a, b, c, d]


def make_coprime(N, c, d):
    """
    Returns (c, d') so d' is congruent to d modulo N, and such that c and d' are
    coprime (<c> + <d'> = R).

    INPUT:

    - ``N`` -- number field ideal

    - ``c`` -- integral element of the number field

    - ``d`` -- integral element of the number field

    OUTPUT:

    A pair (c, d') where c, d' are integral elements of the corresponding
    number field, with d' congruent to d mod N, and such that <c> + <d'> = R
    (R being the corresponding ring of integers).

    EXAMPLES::

        sage: from sage.modular.modsym.p1list_nf import make_coprime
        sage: k.<a> = NumberField(x^2 + 23)
        sage: N = k.ideal(3, a - 1)
        sage: c = 2*a; d = a + 1
        sage: N.is_coprime(k.ideal(c, d))
        True
        sage: k.ideal(c).is_coprime(d)
        False
        sage: c, dp = make_coprime(N, c, d)
        sage: k.ideal(c).is_coprime(dp)
        True
    """
    k = N.number_field()
    if new_is_coprime(k.ideal(c), k.ideal(d)):
        return c, d
    else:
        q = k.ideal(c).prime_to_idealM_part(d)
        it = k.primes_of_degree_one_iter()
        r = k.ideal(1)
        qN = q * N
        while not (new_is_coprime(r, c) and (r * qN).is_principal()):
            r = next(it)
        m = (r * qN).gens_reduced()[0]
        d1 = d + m
        return c, d1


def psi(N):
    r"""
    The index `[\Gamma : \Gamma_0(N)]`, where `\Gamma = GL(2, R)` for `R` the
    corresponding ring of integers, and `\Gamma_0(N)` standard congruence
    subgroup.

    EXAMPLES::

        sage: from sage.modular.modsym.p1list_nf import psi
        sage: k.<a> = NumberField(x^2 + 23)
        sage: N = k.ideal(3, a - 1)
        sage: psi(N)
        4

    ::

        sage: k.<a> = NumberField(x^2 + 23)
        sage: N = k.ideal(5)
        sage: psi(N)
        26
    """
    if not N.is_integral():
        raise ValueError("psi only defined for integral ideals")

    from sage.misc.all import prod

    return prod(
        [
            (np + 1) * np ** (e - 1)
            for np, e in [(p.absolute_norm(), e) for p, e in N.factor()]
        ]
    )


def normalize_tuple(N, elt, with_scalar=False):
    r"""
    Hacked function to replace MSymbol.normalize.
        - removed all check
        - now work with fake MSymbol class that doesn't really do anything
        - sped up some ideal functions (is_coprime) with global hacks

    Previous documentation:

    Return a normalized  element of (a canonical representative of an element
    of `\mathbb{P}^1(R/N)` ) equivalent to ``elt``.

    INPUT:

    - ``elt`` -- a tuple (c,d) that we wish to normalize
    - ``with_scalar`` -- bool (default False)

    OUTPUT:

    - (only if ``with_scalar=True``) a transforming scalar `u`, such that
      `(u*c', u*d')` is congruent to `(c: d)` (mod `N`), where `(c: d)`
      are the coefficients of ``self`` and `N` is the level.

    -  a normalized tuple (c', d') equivalent to ``self`` in P^1(R/N).

    """
    k = N.number_field()
    R = k.ring_of_integers()
    c, d = elt

    if c.mod(N) == 0:
        if with_scalar:
            return N.reduce(d), MyMSymbol(k(0), k(1))
        else:
            return MyMSymbol(k(0), k(1))
    if d.mod(N) == 0:
        if with_scalar:
            return N.reduce(c), MyMSymbol(k(1), k(0))
        else:
            return MyMSymbol(k(1), k(0))
    if new_is_coprime(N, c):
        cinv = R(c).inverse_mod(N)
        if with_scalar:
            return N.reduce(c), MyMSymbol(1, N.reduce(d * cinv))
        else:
            return MyMSymbol(1, N.reduce(d * cinv))

    if N in _level_cache:
        Lfacs, Lxs = _level_cache[N]
    else:
        Lfacs = [p**e for p, e in N.factor()]
        Lxs = [(N / p).element_1_mod(p) for p in Lfacs]
        # Lfacs, Lxs only depend of the ideal: same lists every time we
        # call normalize for a given level, so we store the lists.
        _level_cache[N] = (Lfacs, Lxs)
    u = 0  # normalizer factor
    p_i = 0
    for p in Lfacs:
        if new_is_coprime(p, c):
            inv = c.inverse_mod(p)
        else:
            inv = d.inverse_mod(p)
        u = u + inv * Lxs[p_i]
        p_i = p_i + 1
    c, d = (N.reduce(u * c), N.reduce(u * d))
    if (c - 1).mod(N) == 0:
        c = R(1)
    if with_scalar:
        return u.inverse_mod(N), MyMSymbol(c, d)
    else:
        return MyMSymbol(c, d)


def new_is_coprime(I, J):
    """
    New coprime function
    """
    return (I + J).gens_reduced()[0] == 1


def new_is_zero(I):
    """
    New is zero function
    """
    return I.gens_reduced()[0] == 0
