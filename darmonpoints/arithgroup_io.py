r"""
Persistence of arithmetic groups as plain data.

The groups attached to rational quaternion algebras (``ArithGroup_rationalquaternion``) and the
S-arithmetic groups built on them (``BigArithGroup_class``) are exported to dictionaries of strings,
integers and lists only, which can be written as JSON. Nothing in them depends on Magma or on Sage's
pickling, so a group can be rebuilt in a new session without starting Magma.

All the data is stored exactly:

- rationals as strings ``"a/b"``, quaternions as their 4 coordinates in ``1, i, j, k``,
- words in the generators as lists of integers,
- real numbers as ``[sign * mantissa, exponent, precision]`` (so ``x = sign * mantissa * 2^exponent``,
  exactly representable at that precision), complex numbers as pairs of reals,
- p-adic matrices as rational lifts of their entries together with the precision.

``export_*`` produce the data and ``import_*`` rebuild the groups from it; ``validate_*`` check that
the data is consistent (raising StoredGroupMismatch otherwise) and ``*_invariants`` compute cheap
invariants used to check that a rebuilt group reproduces the original one.

The magma session of a rebuilt group is a LazyMagma, which only starts Magma when some computation
needs it (for example Hecke operators at a new prime). Setting the environment variable
``DARMONPOINTS_FORBID_MAGMA`` to a nonempty value other than ``0`` makes it raise instead.
"""

import datetime
import os
import random
import subprocess

from sage.matrix.constructor import Matrix as matrix
from sage.rings.complex_mpfr import ComplexField
from sage.rings.integer_ring import Z as ZZ
from sage.rings.padics.factory import Qp
from sage.rings.rational_field import Q as QQ
from sage.rings.real_mpfr import RealField

from .util import is_in_Gamma0loc, lift_padic_splitting, multiply_out

SCHEMA_VERSION = 1
FORBID_MAGMA_ENV = "DARMONPOINTS_FORBID_MAGMA"
FUCHSIAN_KIND = "fuchsian_rational_quaternion"
SARITH_KIND = "sarithmetic_rational_quaternion"


class StoredGroupMismatch(ValueError):
    r"""
    The stored data of a group is inconsistent, or does not describe the requested group.
    """


class MagmaForbiddenError(RuntimeError):
    r"""
    Magma was needed while the environment variable DARMONPOINTS_FORBID_MAGMA was set.
    """


def magma_forbidden():
    return os.environ.get(FORBID_MAGMA_ENV, "") not in ("", "0")


class LazyMagma:
    r"""
    A Magma session that is only started when it is used.

    It forwards attribute access and calls to the session, starting it on the first one. The
    session can also be given (``magma``), in which case it is just a wrapper.

    EXAMPLES::

        sage: from darmonpoints.arithgroup_io import LazyMagma
        sage: m = LazyMagma(seed=1)
        sage: m.started()
        False
    """

    def __init__(self, seed=None, server=None, magma=None):
        self._lazy_seed = seed
        self._lazy_server = server
        self._lazy_magma = magma

    def started(self):
        return self._lazy_magma is not None

    def session(self):
        if self._lazy_magma is None:
            if magma_forbidden():
                raise MagmaForbiddenError(
                    "Magma is needed here, but %s is set" % FORBID_MAGMA_ENV
                )
            from sage.interfaces.magma import Magma

            kwds = {}
            if self._lazy_seed is not None:
                kwds["seed"] = self._lazy_seed
            if self._lazy_server is not None:
                kwds["server"] = self._lazy_server
            self._lazy_magma = Magma(**kwds)
        return self._lazy_magma

    def __getattr__(self, name):
        if name.startswith("_lazy") or (name.startswith("__") and name.endswith("__")):
            raise AttributeError(name)
        return getattr(self.session(), name)

    def __call__(self, *args, **kwds):
        return self.session()(*args, **kwds)

    def __repr__(self):
        state = "started" if self.started() else "not started"
        return "Lazy Magma session (%s, seed = %s)" % (state, self._lazy_seed)


def as_lazy_magma(magma=None, seed=None, server=None):
    r"""
    A LazyMagma for ``magma``: itself if it is already one, a wrapper if it is a session, and a
    new unstarted session if it is None.
    """
    if isinstance(magma, LazyMagma):
        return magma
    return LazyMagma(seed=seed, server=server, magma=magma)


def magma_started(magma):
    if magma is None:
        return False
    if isinstance(magma, LazyMagma):
        return magma.started()
    return True


######################
# Encoding of values #
######################


def encode_rational(x):
    return str(QQ(x))


def decode_rational(s):
    return QQ(s)


def encode_quaternion(x):
    return [encode_rational(c) for c in x.coefficient_tuple()]


def decode_quaternion(B, v):
    if len(v) != 4:
        raise StoredGroupMismatch(
            "A quaternion should have 4 coordinates, got %s" % (v,)
        )
    return B([decode_rational(c) for c in v])


def encode_word(w):
    return [int(i) for i in w]


def encode_real(x):
    prec = int(x.prec())
    if x.is_zero():
        return ["0", 0, prec]
    s, m, e = x.sign_mantissa_exponent()
    return [str(ZZ(s) * ZZ(m)), int(e), prec]


def decode_real(v):
    m, e, prec = v
    return RealField(int(prec))(QQ(ZZ(m)) * QQ(2) ** int(e))


def encode_complex(z):
    return [encode_real(z.real()), encode_real(z.imag())]


def decode_complex(v):
    re, im = decode_real(v[0]), decode_real(v[1])
    return ComplexField(re.prec())(re, im)


def encode_real_matrix(M):
    return [encode_real(x) for x in M.list()]


def decode_real_matrix(v, prec):
    return matrix(RealField(prec), 2, 2, [decode_real(x) for x in v])


def encode_padic_matrix(M):
    return [encode_rational(QQ(x.lift())) for x in M.list()]


def decode_padic_splitting(stored, p, prec, a, b):
    r"""
    The matrices I, J (in M_2(Qp(p, prec))) of the stored p-adic splitting: its entries if ``prec``
    is at most the stored precision, and a Hensel lift of them otherwise.
    """
    if ZZ(stored["p"]) != ZZ(p):
        raise StoredGroupMismatch(
            "The stored p-adic splitting is at %s, not at %s" % (stored["p"], p)
        )
    R = Qp(p, prec)
    II = matrix(R, 2, 2, [R(decode_rational(s)) for s in stored["I"]])
    JJ = matrix(R, 2, 2, [R(decode_rational(s)) for s in stored["J"]])
    if prec > int(stored["prec"]):
        II, JJ = lift_padic_splitting(R(a), R(b), II, JJ, p, prec)
    return II, JJ


##########
# Header #
##########


def _git_commit():
    try:
        out = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=os.path.dirname(os.path.abspath(__file__)),
            capture_output=True,
            text=True,
            timeout=10,
        )
        return out.stdout.strip() or None
    except Exception:
        return None


def _magma_version(magma):
    if not magma_started(magma):
        return None
    try:
        return str(magma.version()[1])
    except Exception:
        return None


def make_header(magma=None, seed=None):
    from sage.version import version as sage_version

    return {
        "created": datetime.datetime.now().isoformat(timespec="seconds"),
        "darmonpoints_commit": _git_commit(),
        "sage_version": sage_version,
        "magma_version": _magma_version(magma),
        "seed": None if seed is None else int(seed),
    }


# Keys of the stored data that are not produced by export_*: the header, the invariants recorded to check
# rebuilt groups (see arithgroup_invariants), and references to other files
NON_PAYLOAD_KEYS = ("header", "checks", "files")


def payload(data):
    r"""
    The data produced by export_* (without header, checks or references): what exporting a rebuilt group has
    to reproduce.
    """
    return {k: v for k, v in data.items() if k not in NON_PAYLOAD_KEYS}


def _check_kind(data, kind):
    if data.get("kind") != kind:
        raise StoredGroupMismatch(
            "Expected data of kind %s, got %s" % (kind, data.get("kind"))
        )
    if data.get("schema_version") != SCHEMA_VERSION:
        raise StoredGroupMismatch(
            "Unsupported schema version %s (this code reads version %s)"
            % (data.get("schema_version"), SCHEMA_VERSION)
        )


###################################
# Groups of rational quaternions  #
###################################


def _ideal_generator(I):
    try:
        return ZZ(I)
    except TypeError:
        return ZZ(I.gen())


def export_arithgroup(G, seed=None):
    r"""
    The data of the arithmetic group ``G`` (an ``ArithGroup_rationalquaternion`` with its
    presentation computed), as a dictionary that can be written as JSON.
    """
    from .arithgroup import ArithGroup_rationalquaternion

    if not isinstance(G, ArithGroup_rationalquaternion):
        raise NotImplementedError(
            "Only groups of rational quaternion algebras can be exported"
        )
    if not G._compute_presentation:
        raise ValueError("The presentation of the group has not been computed")
    B = G.B
    a, b = B.invariants()
    try:
        Omax_basis = G._stored_Omax_basis
    except AttributeError:
        from .util import magma_quaternion_to_sage

        Omax_basis = [
            magma_quaternion_to_sage(B, o, G.magma) for o in G._Omax_magma.ZBasis()
        ]
    _, II, JJ, KK = G._splitting_at_infinity(G._prec_inf)
    return {
        "kind": FUCHSIAN_KIND,
        "schema_version": SCHEMA_VERSION,
        "header": make_header(G.magma, seed),
        "abtuple": [encode_rational(a), encode_rational(b)],
        "discriminant": int(G.discriminant),
        "level": int(G.level),
        "grouptype": G._grouptype,
        "O_basis": [encode_quaternion(o) for o in G._get_O_basis()],
        "Omax_basis": [encode_quaternion(o) for o in Omax_basis],
        "order_discriminant": int(_ideal_generator(G.order_discriminant())),
        "Ugens": [encode_quaternion(g) for g in G.Ugens],
        "Uside": [encode_quaternion(g) for g in G.Uside],
        "F_unit_offset": int(G.F_unit_offset),
        "ngquats": int(G.ngquats),
        "gquats": [encode_quaternion(g) for g in G.gquats[1:]],
        "findex": [int(i) for i in G.findex],
        "fdargs": [encode_real(x) for x in G.fdargs],
        "fundamental_domain": [encode_complex(z) for z in G._fundamental_domain],
        "minus_one_long": encode_word(G.minus_one_long),
        "translate": [encode_word(w) for w in G.translate[1:]],
        "relation_words": [encode_word(w) for w in G._relation_words],
        "splitting_at_infinity": {
            "prec": int(G._prec_inf),
            "I": encode_real_matrix(II),
            "J": encode_real_matrix(JJ),
            "K": encode_real_matrix(KK),
        },
    }


def import_arithgroup(data, magma=None, validate=True):
    r"""
    The ``ArithGroup_rationalquaternion`` described by ``data`` (see export_arithgroup), built
    without Magma. Its magma session is ``magma`` (made lazy) or a new LazyMagma.
    """
    from .arithgroup import ArithGroup_rationalquaternion

    _check_kind(data, FUCHSIAN_KIND)
    abtuple = [decode_rational(x) for x in data["abtuple"]]
    G = ArithGroup_rationalquaternion(
        abtuple,
        ZZ(data["level"]),
        grouptype=data["grouptype"],
        magma=as_lazy_magma(magma),
        compute_presentation=True,
        stored_data=data,
    )
    if validate:
        validate_arithgroup(G)
    return G


def _fail(msg):
    raise StoredGroupMismatch(msg)


def _close(x, y, prec):
    # Entrywise, as matrix norms may be computed in double precision
    size = max([1] + [abs(c) for c in y.list()])
    return (
        max(abs(c) for c in (x - y).list())
        <= RealField(prec)(2) ** (-(prec - 40)) * size
    )


def validate_arithgroup(G, expected_order_basis=None):
    r"""
    Check that the data of the rebuilt group ``G`` is consistent, raising StoredGroupMismatch.

    If ``expected_order_basis`` (a list of quaternions, or of their coordinates) is given, also
    check that the order of ``G`` is the one they span.
    """
    B = G.B
    one = B.one()
    if B.discriminant() != G.discriminant:
        _fail(
            "The quaternion algebra has discriminant %s, not %s"
            % (B.discriminant(), G.discriminant)
        )
    if G.O.discriminant() != G.discriminant * G.level:
        _fail(
            "The order has discriminant %s, not %s"
            % (G.O.discriminant(), G.discriminant * G.level)
        )
    if expected_order_basis is not None:
        expected = B.quaternion_order([B(o) for o in expected_order_basis])
        if expected != G.O:
            _fail("The stored order is not the expected order %s" % (expected.basis(),))
    for g in G.Ugens:
        if g.reduced_norm() != 1 or not G._is_in_order(g):
            _fail("Generator %s is not a unit of norm 1 of the order" % g)
    for g in G.gquats[1:]:
        if g.reduced_norm() != 1 or not G._is_in_order(g):
            _fail("Side pairing %s is not a unit of norm 1 of the order" % g)
    n = G.ngquats
    if len(G.gquats) != 2 * n + 1 or len(G.translate) != 2 * n + 1:
        _fail("Expected %s side pairings and translations" % (2 * n))
    if len(G.findex) != len(G.fdargs) + 1 or any(
        abs(i) > n or i == 0 for i in G.findex
    ):
        _fail("Inconsistent fundamental domain indices")
    if any(x >= y for x, y in zip(G.fdargs, G.fdargs[1:])):
        _fail("The fundamental domain arguments are not increasing")
    ngens = len(G.Ugens)
    for w in G._relation_words:
        if any(i == 0 or abs(i) > ngens for i in w):
            _fail("Relation %s uses a nonexisting generator" % w)
        if multiply_out(w, G.Ugens, one) not in (one, -one):
            _fail("Relation %s does not hold" % w)
    for i in range(1, 2 * n + 1):
        w = G.translate[i]
        if any(j == 0 or abs(j) > ngens for j in w):
            _fail("Translation %s uses a nonexisting generator" % i)
        target = G.gquats[i] ** -1
        if multiply_out(w, G.Ugens, one) not in (target, -target):
            _fail("Translation %s does not give the inverse of its side pairing" % i)
    prec = G._prec_inf
    _, II, JJ, KK = G._splitting_at_infinity(prec)
    a, b = B.invariants()
    if not (
        _close(II * II, a * II.parent()(1), prec)
        and _close(JJ * JJ, b * JJ.parent()(1), prec)
        and _close(II * JJ, KK, prec)
        and _close(JJ * II, -KK, prec)
    ):
        _fail("The splitting at infinity is not a splitting of the quaternion algebra")
    return True


def arithgroup_invariants(G, nsamples=20, seed=0, max_length=6):
    r"""
    Cheap invariants of ``G`` that must be the same for a group and its rebuilt copy: the relation
    matrix, the abelian invariants, and the word problem on some products of the generators.
    """
    rng = random.Random(seed)
    Ugens = [g.quaternion_rep for g in G.gens()]
    samples = []
    for _ in range(nsamples):
        length = rng.randint(1, max_length)
        x = G.B.one()
        for _ in range(length):
            i = rng.randrange(len(Ugens))
            x = x * (Ugens[i] if rng.random() < 0.5 else Ugens[i] ** -1)
        samples.append(x)
    words = []
    for x in samples:
        w = G.get_word_rep(x)
        if multiply_out(w, Ugens, G.B.one()) not in (x, -x):
            _fail("The word problem gives a wrong word for %s" % x)
        words.append(encode_word(w))
    return {
        "relation_matrix": [
            [int(c) for c in row] for row in G.get_relation_matrix().rows()
        ],
        "abelian_invariants": [int(c) for c in G.abelianization().abelian_invariants()],
        "samples": [encode_quaternion(x) for x in samples],
        "words": words,
    }


#########################
# S-arithmetic groups   #
#########################


def export_sarithgroup(G, seed=None, padic_prec=None):
    r"""
    The data of the S-arithmetic group ``G`` (a ``BigArithGroup_class`` over QQ) that is not in
    its two arithmetic groups: wp, the representatives of the Bruhat-Tits edges, and the p-adic
    splitting (at the precision it was computed at, or at least ``padic_prec``). The two arithmetic
    groups are exported separately (see export_arithgroup).
    """
    from sage.rings.rational_field import QQ as Q

    if G.F != Q:
        raise NotImplementedError("Only S-arithmetic groups over QQ can be exported")
    if G.use_shapiro():
        raise NotImplementedError("Groups using Shapiro's lemma cannot be exported")
    Gpn = G.small_group()
    try:
        splitting = dict(Gpn._stored_padic_splitting)
    except AttributeError:
        prec = max(G._prec, 200 if padic_prec is None else padic_prec)
        _, II, JJ, _ = G.local_splitting(prec)
        splitting = {
            "p": int(G.p),
            "prec": int(II.base_ring().precision_cap()),
            "I": encode_padic_matrix(II),
            "J": encode_padic_matrix(JJ),
        }
    return {
        "kind": SARITH_KIND,
        "schema_version": SCHEMA_VERSION,
        "header": make_header(G.magma, seed),
        "p": int(G.p),
        "discriminant": int(G.discriminant),
        "level": int(G.level),
        "grouptype": G.Gn._grouptype,
        "abtuple": [encode_rational(x) for x in G.Gn.B.invariants()],
        "Gn_O_basis": [encode_quaternion(o) for o in G.Gn._get_O_basis()],
        "Gpn_O_basis": [encode_quaternion(o) for o in Gpn._get_O_basis()],
        "wp": encode_quaternion(G.wp()),
        "BT_reps": [encode_quaternion(g) for g in G.get_BT_reps()],
        "padic_splitting": splitting,
    }


def import_sarithgroup(data, Gn, Gpn, magma=None, validate=True):
    r"""
    The ``BigArithGroup_class`` described by ``data`` (see export_sarithgroup), built on the
    arithmetic groups ``Gn`` and ``Gpn`` (see import_arithgroup) without Magma.
    """
    from .sarithgroup import BigArithGroup_class

    _check_kind(data, SARITH_KIND)
    B = Gn.B
    if [encode_rational(x) for x in B.invariants()] != data["abtuple"]:
        _fail(
            "The arithmetic groups are not in the quaternion algebra %s"
            % data["abtuple"]
        )
    if Gpn.B is not B:
        _fail("The two arithmetic groups are not in the same quaternion algebra")
    for name, H in (("Gn", Gn), ("Gpn", Gpn)):
        expected = B.quaternion_order(
            [decode_quaternion(B, v) for v in data[name + "_O_basis"]]
        )
        if expected != H.O:
            _fail("The order of %s is not the stored one" % name)
    p, D, N = ZZ(data["p"]), ZZ(data["discriminant"]), ZZ(data["level"])
    if Gn.level != N or Gpn.level != p * N or Gn.discriminant != D:
        _fail(
            "The arithmetic groups do not have the levels N = %s and pN = %s"
            % (N, p * N)
        )
    G = BigArithGroup_class(
        QQ,
        p,
        D,
        abtuple=tuple(B.invariants()),
        level=N,
        magma=as_lazy_magma(magma if magma is not None else Gn.magma),
        grouptype=data["grouptype"],
        use_shapiro=False,
        Gn=Gn,
        Gpn=Gpn,
        padic_splitting=dict(data["padic_splitting"]),
        wp=decode_quaternion(B, data["wp"]),
        BT_reps=[decode_quaternion(B, v) for v in data["BT_reps"]],
    )
    G._stored_data = data
    if validate:
        validate_sarithgroup(G)
    return G


def validate_sarithgroup(G):
    r"""
    Check the data of the rebuilt S-arithmetic group ``G`` (the arithmetic groups are checked by
    validate_arithgroup), raising StoredGroupMismatch.
    """
    Gn, Gpn = G.large_group(), G.small_group()
    B = Gn.B
    p = G.p
    a, b = B.invariants()
    prec = int(Gpn._stored_padic_splitting["prec"])
    _, II, JJ, KK = G.local_splitting(prec)
    one = II.parent()(1)
    if II * II != a * one or JJ * JJ != b * one or II * JJ != -JJ * II:
        _fail("The p-adic splitting is not a splitting of the quaternion algebra")
    for o in Gpn._get_O_basis():
        if not is_in_Gamma0loc(G.embed(o, prec), det_condition=False):
            _fail(
                "The p-adic splitting does not send the order of level pN to an Eichler order"
            )
    # wp was checked when it was set (BigArithGroup_class.set_wp)
    reps = G.get_BT_reps()
    if len(reps) != p + 1 or reps[0] != 1:
        _fail(
            "Expected %s representatives of the Bruhat-Tits edges, starting with 1"
            % (p + 1)
        )
    for r in reps:
        if r.reduced_norm() != 1 or not Gn._is_in_order(r):
            _fail(
                "BT representative %s is not a unit of norm 1 of the order of level N"
                % r
            )
    for i, r in enumerate(reps):
        rinv = r**-1
        for s in reps[:i]:
            if G.is_in_Gpn_order(s * rinv):
                _fail("Two BT representatives are in the same coset")
    return True


def sarithgroup_invariants(G, prec=None):
    r"""
    Invariants of the S-arithmetic group ``G`` that must be the same for a group and its rebuilt
    copy (besides those of its two arithmetic groups). The p-adic splitting is taken at ``prec``
    (by default, the stored precision if there is one, and the current one otherwise).
    """
    if prec is None:
        stored = G.small_group().__dict__.get("_stored_padic_splitting")
        prec = int(stored["prec"]) if stored is not None else G._prec
    _, II, JJ, _ = G.local_splitting(prec)
    return {
        "wp": encode_quaternion(G.wp()),
        "BT_reps": [encode_quaternion(g) for g in G.get_BT_reps()],
        "Up_reps": [encode_quaternion(g) for g in G.get_Up_reps()],
        "padic_splitting": [encode_padic_matrix(II), encode_padic_matrix(JJ)],
    }
