# distutils: sources = darmonpoints/fdom/fdom.c
# distutils: include_dirs = darmonpoints/fdom
# distutils: libraries = pari gmp m
r"""
Interface to James Rickards' library for arithmetic Fuchsian groups.

The C sources are vendored in ``darmonpoints/fdom`` (see the README there).
All functions take and return cypari2 ``Gen`` objects (anything convertible
by ``pari(...)`` is accepted as input), with the same conventions as the GP
package ``fdom.gp``. In particular, ``A`` is an algebra produced by PARI's
``alginit`` (a quaternion algebra over a totally real field, split at exactly
one real place), and ``X`` is the structure returned by :func:`afuchinit`.

EXAMPLES::

    sage: from darmonpoints.afuch import afuchinit, afuchsignature, afuchpresentation, afuchword
    sage: A = pari('alginit(nfinit(y), [-1, 3])')
    sage: X = afuchinit(A)
    sage: afuchsignature(X)
    [0, Vecsmall([2, 2, 3, 3]), 0]
    sage: gens = afuchpresentation(X)[0]
    sage: len(gens)
    3
    sage: g = pari('algmul')(A, gens[0], gens[1])
    sage: afuchword(X, g)
    Vecsmall([1, 2])
"""

from cypari2.gen cimport Gen, objtogen
from cypari2.paridecl cimport nbits2prec
from cypari2.stack cimport clear_stack, new_gen
from cypari2.types cimport GEN
from cysignals.signals cimport sig_on


cdef extern from "fdom.h":
    GEN c_afuchinit "afuchinit"(GEN A, GEN O, GEN type, int flag, long prec)
    GEN c_afuchmoreprec "afuchmoreprec"(GEN X, long inc)
    GEN c_afuchnewp "afuchnewp"(GEN X, GEN p)
    GEN c_afuchnewtype "afuchnewtype"(GEN X, GEN type)
    GEN c_afuchactions "afuchactions"(GEN X)
    GEN c_afuchalg "afuchalg"(GEN X)
    GEN c_afucharea "afucharea"(GEN X)
    GEN c_afuchelliptic "afuchelliptic"(GEN X)
    GEN c_afuchelts "afuchelts"(GEN X)
    int c_afuchelttype "afuchelttype"(GEN X, GEN g)
    GEN c_afuchmakefdom "afuchmakefdom"(GEN X)
    GEN c_afuchgeodesic "afuchgeodesic"(GEN X, GEN g)
    GEN c_afuchminimalcycles "afuchminimalcycles"(GEN X)
    GEN c_afuchnormalizernorms "afuchnormalizernorms"(GEN X)
    GEN c_afuchorder "afuchorder"(GEN X)
    GEN c_afuchpresentation "afuchpresentation"(GEN X)
    GEN c_afuchsides "afuchsides"(GEN X)
    GEN c_afuchsignature "afuchsignature"(GEN X)
    GEN c_afuchspair "afuchspair"(GEN X)
    GEN c_afuchword "afuchword"(GEN X, GEN g)
    GEN c_afuchvertices "afuchvertices"(GEN X, int model)
    GEN c_afuchfindoneelt "afuchfindoneelt"(GEN X, GEN nm, GEN C)
    GEN c_algab "algab"(GEN A)
    GEN c_algalgto1ijk "algalgto1ijk"(GEN A, GEN x)
    GEN c_algbasisto1ijk "algbasisto1ijk"(GEN A, GEN x)
    GEN c_alg1ijktoalg "alg1ijktoalg"(GEN A, GEN x)
    GEN c_alg1ijktobasis "alg1ijktobasis"(GEN A, GEN x)
    GEN c_algramifiedplacesf "algramifiedplacesf"(GEN A)
    GEN c_algreduceddisc "algreduceddisc"(GEN A)
    long c_algsplitoo "algsplitoo"(GEN A)
    int c_algisorder "algisorder"(GEN A, GEN O)
    GEN c_algorderlevel "algorderlevel"(GEN A, GEN O, int factored)


cdef GEN _opt(Gen x):
    return NULL if x is None else x.g


def afuchinit(A, O=None, type=None, long flag=1, long bitprec=128):
    r"""
    Initialize the arithmetic Fuchsian group attached to the order ``O`` of
    the algebra ``A`` (default: the maximal order stored in ``A``).

    ``O`` is a square matrix whose columns are the coordinates of a `\ZZ`-basis
    of the order in the basis of the stored maximal order. ``type`` is 0 for
    `O^1` (default), 1 for totally positive unit norm, 2 for `AL(O)^+`, 3 for
    the positive normalizer. If ``flag`` is 1, the fundamental domain and
    presentation are also computed. The computation uses the Klein model with
    `p = \pi/8 + i/2` sent to 0.
    """
    cdef Gen A_ = objtogen(A)
    cdef Gen O_ = None if O is None else objtogen(O)
    cdef Gen t_ = None if type is None else objtogen(type)
    sig_on()
    return new_gen(c_afuchinit(A_.g, _opt(O_), _opt(t_), flag, nbits2prec(bitprec)))


def afuchmoreprec(X, long inc=1):
    cdef Gen X_ = objtogen(X)
    sig_on()
    return new_gen(c_afuchmoreprec(X_.g, inc))


def afuchnewp(X, p):
    cdef Gen X_ = objtogen(X)
    cdef Gen p_ = objtogen(p)
    sig_on()
    return new_gen(c_afuchnewp(X_.g, p_.g))


def afuchnewtype(X, type):
    cdef Gen X_ = objtogen(X)
    cdef Gen t_ = objtogen(type)
    sig_on()
    return new_gen(c_afuchnewtype(X_.g, t_.g))


def afuchactions(X):
    cdef Gen X_ = objtogen(X)
    sig_on()
    return new_gen(c_afuchactions(X_.g))


def afuchalg(X):
    cdef Gen X_ = objtogen(X)
    sig_on()
    return new_gen(c_afuchalg(X_.g))


def afucharea(X):
    cdef Gen X_ = objtogen(X)
    sig_on()
    return new_gen(c_afucharea(X_.g))


def afuchelliptic(X):
    cdef Gen X_ = objtogen(X)
    sig_on()
    return new_gen(c_afuchelliptic(X_.g))


def afuchelts(X):
    r"""
    Elements giving the sides of the stored fundamental domain (in the basis
    of the stored maximal order).
    """
    cdef Gen X_ = objtogen(X)
    sig_on()
    return new_gen(c_afuchelts(X_.g))


def afuchelttype(X, g):
    cdef Gen X_ = objtogen(X)
    cdef Gen g_ = objtogen(g)
    cdef int ans
    sig_on()
    ans = c_afuchelttype(X_.g, g_.g)
    clear_stack()
    return ans


def afuchmakefdom(X):
    cdef Gen X_ = objtogen(X)
    sig_on()
    return new_gen(c_afuchmakefdom(X_.g))


def afuchgeodesic(X, g):
    cdef Gen X_ = objtogen(X)
    cdef Gen g_ = objtogen(g)
    sig_on()
    return new_gen(c_afuchgeodesic(X_.g, g_.g))


def afuchminimalcycles(X):
    cdef Gen X_ = objtogen(X)
    sig_on()
    return new_gen(c_afuchminimalcycles(X_.g))


def afuchnormalizernorms(X):
    cdef Gen X_ = objtogen(X)
    sig_on()
    return new_gen(c_afuchnormalizernorms(X_.g))


def afuchorder(X):
    cdef Gen X_ = objtogen(X)
    sig_on()
    return new_gen(c_afuchorder(X_.g))


def afuchpresentation(X):
    r"""
    Return ``[gens, rels]``. A relation ``Vecsmall([1, -4, 3])`` means that
    ``gens[1] * gens[4]^-1 * gens[3]`` lies in the centre of the algebra.
    """
    cdef Gen X_ = objtogen(X)
    sig_on()
    return new_gen(c_afuchpresentation(X_.g))


def afuchsides(X):
    cdef Gen X_ = objtogen(X)
    sig_on()
    return new_gen(c_afuchsides(X_.g))


def afuchsignature(X):
    r"""
    Return ``[genus, Vecsmall(elliptic orders), number of cusps]``.
    """
    cdef Gen X_ = objtogen(X)
    sig_on()
    return new_gen(c_afuchsignature(X_.g))


def afuchspair(X):
    cdef Gen X_ = objtogen(X)
    sig_on()
    return new_gen(c_afuchspair(X_.g))


def afuchword(X, g):
    r"""
    Write ``g`` (in the basis of the stored maximal order) as a word in the
    generators of :func:`afuchpresentation`, up to the centre.
    """
    cdef Gen X_ = objtogen(X)
    cdef Gen g_ = objtogen(g)
    sig_on()
    return new_gen(c_afuchword(X_.g, g_.g))


def afuchvertices(X, int model=0):
    cdef Gen X_ = objtogen(X)
    sig_on()
    return new_gen(c_afuchvertices(X_.g, model))


def afuchfindoneelt(X, nm=1, C=None):
    r"""
    Return a primitive element of the order of ``X``, of reduced norm ``nm``,
    in the normalizer of the order. Loops forever if no such element exists.
    """
    cdef Gen X_ = objtogen(X)
    cdef Gen nm_ = objtogen(nm)
    cdef Gen C_ = None if C is None else objtogen(C)
    sig_on()
    return new_gen(c_afuchfindoneelt(X_.g, nm_.g, _opt(C_)))


def algab(A):
    cdef Gen A_ = objtogen(A)
    sig_on()
    return new_gen(c_algab(A_.g))


def algalgto1ijk(A, x):
    cdef Gen A_ = objtogen(A)
    cdef Gen x_ = objtogen(x)
    sig_on()
    return new_gen(c_algalgto1ijk(A_.g, x_.g))


def algbasisto1ijk(A, x):
    cdef Gen A_ = objtogen(A)
    cdef Gen x_ = objtogen(x)
    sig_on()
    return new_gen(c_algbasisto1ijk(A_.g, x_.g))


def alg1ijktoalg(A, x):
    cdef Gen A_ = objtogen(A)
    cdef Gen x_ = objtogen(x)
    sig_on()
    return new_gen(c_alg1ijktoalg(A_.g, x_.g))


def alg1ijktobasis(A, x):
    cdef Gen A_ = objtogen(A)
    cdef Gen x_ = objtogen(x)
    sig_on()
    return new_gen(c_alg1ijktobasis(A_.g, x_.g))


def algramifiedplacesf(A):
    cdef Gen A_ = objtogen(A)
    sig_on()
    return new_gen(c_algramifiedplacesf(A_.g))


def algreduceddisc(A):
    cdef Gen A_ = objtogen(A)
    sig_on()
    return new_gen(c_algreduceddisc(A_.g))


def algsplitoo(A):
    cdef Gen A_ = objtogen(A)
    cdef long ans
    sig_on()
    ans = c_algsplitoo(A_.g)
    clear_stack()
    return ans


def algisorder(A, O):
    cdef Gen A_ = objtogen(A)
    cdef Gen O_ = objtogen(O)
    cdef int ans
    sig_on()
    ans = c_algisorder(A_.g, O_.g)
    clear_stack()
    return bool(ans)


def algorderlevel(A, O, int factored=0):
    cdef Gen A_ = objtogen(A)
    cdef Gen O_ = objtogen(O)
    sig_on()
    return new_gen(c_algorderlevel(A_.g, O_.g, factored))
