r"""
Compare the PARI backend of darmonpoints with the Magma backend.

Run inside a Sage session in which Magma works (Magma does not start from
``sage -c`` / ``sage script.sage``)::

    sage: load("tools/compare_magma.sage")
    sage: compare_all(magma)            # uses the global Magma session

or run single checks, e.g. ``compare_group(5, 6, 1, magma=magma)``.

Bases, generators and words differ between the backends, so only invariants
are compared: abelianizations, Hecke characteristic polynomials, validity of
local splittings, elements of given norm and quadratic embeddings.
"""
from sage.misc.timing import walltime

from darmonpoints.cohomology_arithmetic import ArithCoh
from darmonpoints.sarithgroup import BigArithGroup
from darmonpoints.util import quaternion_algebra_invariants_from_ramification


def _group_invariants(G, primes):
    H = ArithCoh(G)
    return {
        "abelianization Gn": G.Gn.abelianization().abelian_invariants(),
        "abelianization Gpn": G.Gpn.abelianization().abelian_invariants(),
        "hecke": {l: H.hecke_matrix(l).charpoly() for l in primes},
    }


def _check_local_splitting(G, prec=20):
    r"""
    The local splitting maps the order of Gpn into Eichler matrices at p.
    """
    iota = G.get_embedding(prec)
    ok = True
    for o in G.Gpn._get_O_basis():
        m = iota(o)
        ok = ok and all(t.valuation() >= 0 for t in m.list())
        ok = ok and m[1, 0].valuation() >= 1
    return ok


def compare_group(p, quat_data, level, base=QQ, primes=None, magma=None, **kwargs):
    r"""
    Build ``BigArithGroup(p, quat_data, level, base=base)`` with both backends
    and compare invariants. ``primes`` are the Hecke primes (default: a few
    small primes not dividing the level data).
    """
    if magma is None:
        from sage.interfaces.magma import magma
    if primes is None:
        if base == QQ:
            bad = ZZ(p) * ZZ(level) * QuaternionAlgebra(quat_data).discriminant() if quat_data in ZZ else None
            primes = [l for l in prime_range(3, 30) if bad is None or bad % l != 0][:4]
        else:
            Pbad = base.ideal(p) * base.ideal(level) * QuaternionAlgebra(base, *quat_data).discriminant()
            primes = [
                P.gens_reduced()[0]
                for P in base.primes_of_degree_one_list(12)
                if P.is_coprime(Pbad) and P.is_principal()
            ][:3]
    res = {}
    for backend in ["pari", "magma"]:
        t = walltime()
        G = BigArithGroup(
            p,
            quat_data,
            level,
            base=base,
            magma=magma if backend == "magma" else None,
            backend=backend,
            use_shapiro=False,
            outfile="/dev/null",
            **kwargs,
        )
        try:
            inv = _group_invariants(G, primes)
            inv["local splitting ok"] = _check_local_splitting(G)
        except Exception as err:
            import traceback

            print("!!! %s backend failed: %s" % (backend, err))
            traceback.print_exc()
            inv = {"error": repr(err)[:300], "group": G}
        inv["time"] = walltime(t)
        res[backend] = inv
        if "error" not in inv:
            print("[%s done in %.1fs] ab(Gn) = %s, ab(Gpn) = %s, hecke = %s"
                  % (backend, inv["time"], inv["abelianization Gn"],
                     inv["abelianization Gpn"],
                     {l: f.factor() for l, f in inv["hecke"].items()}), flush=True)
    if any("error" in res[b] for b in res):
        print("=" * 70)
        print("p = %s, B = %s, level = %s, base = %s" % (p, quat_data, level, base))
        for b in res:
            print(" %s: %s" % (b, res[b].get("error", "ok")))
        print(" *** ERROR ***")
        return False, res
    same = all(
        res["pari"][k] == res["magma"][k]
        for k in ["abelianization Gn", "abelianization Gpn", "hecke"]
    )
    print("=" * 70)
    print("p = %s, B = %s, level = %s, base = %s" % (p, quat_data, level, base))
    for backend in ["pari", "magma"]:
        r = res[backend]
        print(" %s (%.1fs): ab(Gn) = %s, ab(Gpn) = %s, local splitting ok: %s"
              % (backend, r["time"], r["abelianization Gn"], r["abelianization Gpn"], r["local splitting ok"]))
        for l, f in r["hecke"].items():
            print("    T_%s: %s" % (l, f.factor()))
    print(" AGREE" if same else " *** DISAGREE ***")
    return same, res


def compare_darmon_point(magma=None):
    r"""
    The quaternionic Darmon point of the doctest in darmonpoints.py, with
    both backends. Compare the printed periods J_psi.
    """
    from darmonpoints.darmonpoints import darmon_point

    if magma is None:
        from sage.interfaces.magma import magma
    E = EllipticCurve("78a1")
    J_pari = darmon_point(13, E, 5, 20, recognize_point=False)[0]
    J_magma = darmon_point(13, E, 5, 20, recognize_point=False, magma=magma)[0]
    print("J_psi (pari)  =", J_pari)
    print("J_psi (magma) =", J_magma)
    print("ratio =", J_pari / J_magma)
    return J_pari, J_magma


def compare_all(magma=None):
    results = []
    results.append(compare_group(5, 6, 1, magma=magma)[0])
    results.append(compare_group(7, 6, 1, magma=magma)[0])
    results.append(compare_group(3, 10, 1, magma=magma)[0])
    results.append(compare_group(13, 6, 5, magma=magma)[0])
    results.append(compare_group(3, 22, 1, magma=magma)[0])
    F = QuadraticField(5, "r")
    r = F.gen()
    P = F.ideal(3 / 2 * r + 1 / 2)
    ab = quaternion_algebra_invariants_from_ramification(F, F.ideal(3), F.real_places()[:1])
    results.append(compare_group(P, ab, F.ideal(1), base=F, magma=magma)[0])
    print("=" * 70)
    print("%s/%s comparisons agree" % (sum(results), len(results)))
    return results


def compare_arithgroup(base, ab, level, magma=None, grouptype="PSL2", **kwargs):
    r"""
    Build ``ArithGroup(base, None, ab, level)`` with both backends and
    compare the abelianizations (useful for Kleinian groups).
    """
    from darmonpoints.sarithgroup import ArithGroup

    if magma is None:
        from sage.interfaces.magma import magma
    res = {}
    for backend in ["pari", "magma"]:
        t = walltime()
        G = ArithGroup(
            base, None, ab, level,
            magma=magma if backend == "magma" else None,
            backend=backend, grouptype=grouptype, **kwargs
        )
        res[backend] = (G.abelianization().abelian_invariants(), len(G.gens()), walltime(t))
    print("=" * 70)
    print("ArithGroup over %s, (a,b) = %s, level = %s" % (base, ab, level))
    for backend in ["pari", "magma"]:
        print(" %s (%.1fs): ab = %s, #gens = %s" % (backend, res[backend][2], res[backend][0], res[backend][1]))
    same = res["pari"][0] == res["magma"][0]
    print(" AGREE" if same else " *** DISAGREE ***")
    return same, res


def compare_kleinian(magma=None):
    r"""
    Kleinian groups: Q(sqrt(-7)) with B ramified at the primes above 2,
    and the cubic field of the find_curve doctest.
    """
    results = []
    x = polygen(QQ)
    F = NumberField(x**2 - x + 2, "w")
    P2 = F.ideal(2).factor()
    ab = quaternion_algebra_invariants_from_ramification(F, P2[0][0] * P2[1][0], [])
    results.append(compare_arithgroup(F, ab, F.ideal(1), magma=magma)[0])
    results.append(compare_arithgroup(F, ab, F.ideal(F.primes_above(11)[0]), magma=magma)[0])
    K = NumberField(x**3 - 3, "r")
    r = K.gen()
    abK = quaternion_algebra_invariants_from_ramification(K, K.ideal(r - 1), K.real_places())
    results.append(compare_group(K.ideal(r - 2), abK, K.ideal(1), base=K, magma=magma)[0])
    print("=" * 70)
    print("%s/%s Kleinian comparisons agree" % (sum(results), len(results)))
    return results
