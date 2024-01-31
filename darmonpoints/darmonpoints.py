##########################################################################
### Darmon (Stark-Heegner) points for quaternion algebras                #
##########################################################################
import configparser
import datetime
import os
import sys
from itertools import product

from sage.algebras.quatalg.quaternion_algebra import QuaternionAlgebra
from sage.arith.misc import factor, fundamental_discriminant
from sage.misc.all import walltime
from sage.misc.misc_c import prod
from sage.misc.verbose import get_verbose, set_verbose, verbose
from sage.rings.all import QQ, RR, ZZ, Qp, Zmod
from sage.rings.infinity import Infinity
from sage.rings.number_field.number_field import is_fundamental_discriminant
from sage.rings.padics.precision_error import PrecisionError
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.schemes.curves.constructor import Curve

from .cohomology_arithmetic import *
from .homology import *
from .integrals import double_integral_zero_infty, integrate_H1
from .limits import find_optimal_embeddings, find_tau0_and_gtau, num_evals
from .sarithgroup import BigArithGroup
from .util import (
    Bunch,
    config_section_map,
    fwrite,
    get_heegner_params,
    quaternion_algebra_invariants_from_ramification,
    recognize_J,
)

r"""
    TESTS:

    sage: from darmonpoints.darmonpoints import darmon_point
    sage: P = darmon_point(13,EllipticCurve('78a1'),5,20); P #  optional - magma
    Starting computation of the Darmon point
    ...
    (22 : 48*alpha - 11 : 1)

"""


def darmon_discriminants(bound, split_primes=None, inert_primes=None):
    good_D = []
    for D in range(2, bound):
        if not is_fundamental_discriminant(D):
            continue
        if not all(ZZ(D).kronecker(p) == 1 for p in split_primes):
            continue
        if not all(ZZ(D).kronecker(p) == -1 for p in inert_primes):
            continue
        good_D.append(D)
    return good_D


def construct_homology_cycle(
    P,
    G,
    D,
    prec,
    hecke_poly_getter,
    outfile=None,
    max_n=None,
    elliptic_curve=None,
    smoothen_prime=None,
    **kwargs,
):
    F_to_Qp = G.base_ring_local_embedding(prec)
    G = G.Gn
    F = G.base_ring()
    t = PolynomialRing(F, names="t").gen()
    K = F.extension(t * t - D, names="beta")
    if F.degree() == 1:
        assert len(K.embeddings(RR)) == 2
    else:
        if len(F.embeddings(RR)) > 1:
            raise NotImplementedError
        elif len(F.embeddings(RR)) == 1:
            if F.degree() != 3:
                raise NotImplementedError
            assert len(K.embeddings(RR)) == 0

    # Choose the prime to do Hecke smoothen later
    if smoothen_prime is None:
        q = ZZ(2)
        Nbad = P * G.order_discriminant() * G.level
        try:
            Nbad = Nbad.norm()
        except AttributeError:
            pass
        try:
            Nbad = Nbad.gens_reduced()[0]
        except AttributeError:
            pass
        while Nbad % q == 0:
            q = q.next_prime()
    else:
        q = smoothen_prime

    if F == QQ:
        q1 = q
    else:
        q1 = F.ideal(q).factor()[0][0]
        a_ell = None
    verbose("q1 = %s" % q1)

    gamma, tau1 = G.embed_order(
        P, D, prec, outfile=outfile, return_all=False, F_to_Qp=F_to_Qp, **kwargs
    )
    Div = Divisors(tau1.parent())
    H1 = OneChains(G, Div)
    D1 = Div(tau1)
    ans = H1({gamma: D1})
    assert ans.is_cycle()
    # Do hecke_smoothen to kill Eisenstein part
    if q1 != 1:
        ans = ans.hecke_smoothen(q1, prec=prec)

    if elliptic_curve is None:
        # Find zero degree equivalent
        ans, n = ans.zero_degree_equivalent(allow_multiple=True)
        return ans, n, q1
    else:
        if F == QQ:
            a_ell = elliptic_curve.ap(q1)
        else:
            Q = F.ideal(q1).factor()[0][0]
            a_ell = ZZ(Q.norm() + 1 - elliptic_curve.reduction(Q).count_points())
        f = hecke_poly_getter(q1)
        R = f.parent()
        x = R.gen()
        while True:
            try:
                f = R(f / (x - a_ell))
            except TypeError:
                break
        while True:
            try:
                f = R(f / (x - (q1 + 1)))
            except TypeError:
                break
        f0 = f.parent()(1)
        for g, e in f.factor():
            ans = ans.act_by_poly_hecke(q1, g**e, prec=prec)
            f0 *= g**e
            try:
                ans, n = ans.zero_degree_equivalent(allow_multiple=True)
                verbose("f0 = %s" % f0)
                return ans, n * f0(a_ell), q1
            except ValueError:
                pass
        verbose("Passed the check!")
    # Find zero degree equivalent
    ans, n = ans.zero_degree_equivalent(allow_multiple=True)
    return ans, n * f(a_ell), q1


def darmon_point(
    P,
    E,
    beta,
    prec,
    ramification_at_infinity=None,
    input_data=None,
    magma=None,
    working_prec=None,
    recognize_point=True,
    **kwargs,
):
    r"""

    EXAMPLES:

    We first need to import the module::

    sage: from darmonpoints.darmonpoints import darmon_point

    A first example (Stark--Heegner point)::

    sage: from darmonpoints.darmonpoints import darmon_point
    sage: darmon_point(7,EllipticCurve('35a1'),41,20, cohomological=False, use_magma=False, use_ps_dists = True)[0]
    Starting computation of the Darmon point
    ...
    -70*alpha + 449

    A quaternionic (Greenberg) point::

    sage: darmon_point(13,EllipticCurve('78a1'),5,20) # long time # optional - magma

    A Darmon point over a cubic (1,1) field::

    sage: F.<r> = NumberField(x^3 - x^2 - x + 2)
    sage: E = EllipticCurve([-r -1, -r, -r - 1,-r - 1, 0])
    sage: N = E.conductor()
    sage: P = F.ideal(r^2 - 2*r - 1)
    sage: beta = -3*r^2 + 9*r - 6
    sage: darmon_point(P,E,beta,20) # long time # optional - magma

    """
    # global G, Coh, phiE, Phi, dK, J, J1, cycleGn, nn, Jlist
    config = configparser.ConfigParser()
    config.read("config.ini")
    param_dict = config_section_map(config, "General")
    param_dict.update(config_section_map(config, "DarmonPoint"))
    param_dict.update(kwargs)
    param = Bunch(**param_dict)

    # Get general parameters
    outfile = param.get("outfile")
    use_ps_dists = param.get("use_ps_dists", False)
    use_shapiro = param.get("use_shapiro", False)
    use_sage_db = param.get("use_sage_db", False)
    magma_seed = param.get("magma_seed", 1515316)
    use_magma = param.get("use_magma", True)
    progress_bar = param.get("progress_bar", True)
    sign_at_infinity = param.get("sign_at_infinity", ZZ(1))

    # Get darmon_point specific parameters
    idx_orientation = param.get("idx_orientation")
    idx_embedding = param.get("idx_embedding", 0)
    algorithm = param.get("algorithm")
    quaternionic = param.get("quaternionic")
    cohomological = param.get("cohomological", True)

    if working_prec is None:
        working_prec = max([2 * prec + 10, 30])

    if use_magma:
        page_path = param.get("page_path", os.path.dirname(__file__))
        page_path += "/KleinianGroups-1.0/klngpspec"
        if magma is None:
            from sage.interfaces.magma import Magma

            magma = Magma()
            quit_when_done = True
        else:
            quit_when_done = False
        print("Using Magma version : %s" % str(magma.version()))
        magma.attach_spec(page_path)
    else:
        quit_when_done = False

    sys.setrecursionlimit(10**6)

    F = E.base_ring()
    beta = F(beta)
    DB, Np, Ncartan = get_heegner_params(P, E, beta)
    if quaternionic is None:
        quaternionic = DB != 1
    if cohomological is None:
        cohomological = quaternionic
    if quaternionic and not cohomological:
        raise ValueError("Need cohomological algorithm when dealing with quaternions")
    if use_ps_dists is None:
        use_ps_dists = False if cohomological else True
    try:
        p = ZZ(P)
    except TypeError:
        p = ZZ(P.norm())
    if not p.is_prime():
        raise ValueError("P (= %s) should be a prime, of inertia degree 1" % P)

    Jlist = []
    if F == QQ:
        dK = ZZ(beta)
        extra_conductor_sq = dK / fundamental_discriminant(dK)
        assert ZZ(extra_conductor_sq).is_square()
        extra_conductor = extra_conductor_sq.sqrt()
        dK = dK / extra_conductor_sq
        assert dK == fundamental_discriminant(dK)
        if dK % 4 == 0:
            dK = ZZ(dK / 4)
        beta = dK
    else:
        dK = beta

    x = QQ["x"].gen()
    K = F.extension(x * x - dK, names="alpha")
    if F == QQ:
        dK = K.discriminant()
    else:
        dK = K.relative_discriminant()

    hK = K.class_number()

    sgninfty = "plus" if sign_at_infinity == 1 else "minus"
    if hasattr(E, "cremona_label"):
        Ename = E.cremona_label()
    elif hasattr(E, "ainvs"):
        Ename = E.ainvs()
    else:
        Ename = "unknown"
    fname = "moments_%s_%s_%s_%s.sobj" % (P, Ename, sgninfty, prec)

    if use_sage_db:
        print("Moments will be stored in database as %s" % (fname))

    if outfile == "log":
        outfile = "%s_%s_%s_%s_%s_%s.log" % (
            P,
            Ename,
            dK,
            sgninfty,
            prec,
            datetime.datetime.now().strftime("%Y%m%d-%H%M%S"),
        )
        outfile = outfile.replace("/", "div")
        outfile = "/tmp/darmonpoint_" + outfile

    fwrite("Starting computation of the Darmon point", outfile)
    fwrite(f"## fname = {fname}", outfile)
    fwrite("D_B = %s  %s" % (DB, factor(DB)), outfile)
    fwrite("Np = %s" % Np, outfile)
    if Ncartan is not None:
        fwrite("Ncartan = %s" % Ncartan, outfile)
    fwrite("dK = %s (class number = %s)" % (dK, hK), outfile)
    fwrite("Calculation with p = %s and prec = %s" % (P, prec), outfile)
    fwrite("Elliptic curve %s: %s" % (Ename, E), outfile)
    if outfile is not None:
        print("Partial results will be saved in %s" % outfile)

    if input_data is None:
        if cohomological:
            # Define the S-arithmetic group
            if F != QQ and ramification_at_infinity is None:
                if F.signature()[0] > 1:
                    if F.signature()[1] == 1:
                        ramification_at_infinity = F.real_places(
                            prec=Infinity
                        )  # Totally 'definite'
                    else:
                        raise ValueError("Please specify the ramification at infinity")
                elif F.signature()[0] == 1:
                    if len(F.ideal(DB).factor()) % 2 == 0:
                        ramification_at_infinity = []  # Split at infinity
                    else:
                        ramification_at_infinity = F.real_places(
                            prec=Infinity
                        )  # Ramified at infinity
                else:
                    ramification_at_infinity = None
            if F == QQ:
                abtuple = QuaternionAlgebra(DB).invariants()
            else:
                abtuple = quaternion_algebra_invariants_from_ramification(
                    F, DB, ramification_at_infinity, magma=magma
                )

            G = kwargs.pop("G", None)
            if G is None:
                fwrite(f"# Initializing S-arithmetic group...", outfile)
                print(f"abtuple = {abtuple} Np = {Np} F = {F}", outfile)
                G = BigArithGroup(
                    P,
                    abtuple,
                    Np,
                    base=F,
                    outfile=outfile,
                    seed=magma_seed,
                    use_sage_db=use_sage_db,
                    magma=magma,
                    use_shapiro=use_shapiro,
                    nscartan=Ncartan,
                )
            # Define the cycle ( in H_1(G,Div^0 Hp) )
            Coh = ArithCoh(G)
            while True:
                try:
                    cycleGn, nn, ell = construct_homology_cycle(
                        p,
                        G,
                        beta,
                        working_prec,
                        lambda q: Coh.hecke_matrix(q).minpoly(),
                        outfile=outfile,
                        elliptic_curve=E,
                        smoothen_prime=kwargs.get("smoothen_prime", None),
                        **kwargs,
                    )
                    break
                except PrecisionError:
                    working_prec *= 2
                    verbose(
                        "Encountered precision error, trying with higher precision (= %s)"
                        % working_prec
                    )
                except ValueError as e:
                    fwrite(
                        "ValueError occurred when constructing homology cycle.", outfile
                    )
                    fwrite("Error : %s" % str(e), outfile)
                    fwrite("Returning the S-arithmetic group.", outfile)
                    if quit_when_done:
                        magma.quit()
                    return G
                except AssertionError as e:
                    fwrite(
                        "Assertion occurred when constructing homology cycle. Returning the S-arithmetic group.",
                        outfile,
                    )
                    fwrite("%s" % str(e), outfile)
                    if quit_when_done:
                        magma.quit()
                    return G
            eisenstein_constant = -ZZ(E.reduction(ell).count_points())
            fwrite(
                "r = %s, so a_r(E) - r - 1 = %s" % (ell, eisenstein_constant), outfile
            )
            fwrite("exponent = %s" % nn, outfile)
            phiE = get_cocycle_from_elliptic_curve(Coh, E, sign=sign_at_infinity)
            if hasattr(E, "ap"):
                sign_ap = E.ap(P)
            else:
                try:
                    sign_ap = ZZ(P.norm() + 1 - E.reduction(P).count_points())
                except ValueError:
                    sign_ap = ZZ(
                        P.norm()
                        + 1
                        - Curve(E).change_ring(P.residue_field()).count_points(1)[0]
                    )

            Phi = get_overconvergent_class_quaternionic(
                P,
                phiE,
                G,
                prec,
                sign_at_infinity,
                sign_ap,
                use_ps_dists=use_ps_dists,
                use_sage_db=use_sage_db,
                progress_bar=progress_bar,
                Ename=Ename,
            )
            # Integration with moments
            tot_time = walltime()
            J = integrate_H1(
                G,
                cycleGn,
                Phi,
                1,
                prec=working_prec,
                twist=True,
                progress_bar=progress_bar,
            )
            verbose("integration tot_time = %s" % walltime(tot_time))
            if use_sage_db:
                G.save_to_db()
        else:  # not cohomological
            nn = 1
            eisenstein_constant = 1
            if algorithm is None:
                if Np == 1:
                    algorithm = "darmon_pollack"
                else:
                    algorithm = "guitart_masdeu"
            w = K.maximal_order().ring_generators()[0]
            r0, r1 = w.coordinates_in_terms_of_powers()(K.gen())
            QQp = Qp(p, working_prec)
            Cp = QQp.extension(w.minpoly().change_ring(QQp), names="g")
            v0 = K.hom([r0 + r1 * Cp.gen()])

            # Optimal embeddings of level one
            fwrite("Computing optimal embeddings of level one...", outfile)
            Wlist = find_optimal_embeddings(
                K, use_magma=use_magma, extra_conductor=extra_conductor, magma=magma
            )
            fwrite("Found %s such embeddings." % len(Wlist), outfile)
            if idx_embedding is not None:
                if idx_embedding >= len(Wlist):
                    fwrite(
                        "There are not enough embeddings. Taking the index modulo %s"
                        % len(Wlist),
                        outfile,
                    )
                    idx_embedding = idx_embedding % len(Wlist)
                fwrite("Taking only embedding number %s" % (idx_embedding), outfile)
                Wlist = [Wlist[idx_embedding]]

            # Find the orientations
            orients = (
                K.maximal_order()
                .ring_generators()[0]
                .minpoly()
                .roots(Zmod(Np), multiplicities=False)
            )
            fwrite("Possible orientations: %s" % orients, outfile)
            if len(Wlist) == 1 or idx_orientation == -1:
                fwrite("Using all orientations, since hK = 1", outfile)
                chosen_orientation = None
            else:
                fwrite("Using orientation = %s" % orients[idx_orientation], outfile)
                chosen_orientation = orients[idx_orientation]

            emblist = []
            for i, W in enumerate(Wlist):
                tau, gtau, sign, limits = find_tau0_and_gtau(
                    v0,
                    Np,
                    W,
                    algorithm=algorithm,
                    orientation=chosen_orientation,
                    extra_conductor=extra_conductor,
                )
                fwrite(
                    "n_evals = %s" % sum((num_evals(t1, t2) for t1, t2 in limits)),
                    outfile,
                )
                emblist.append((tau, gtau, sign, limits))

            # Get the cohomology class from E
            Phi = get_overconvergent_class_matrices(
                P,
                E,
                prec,
                sign_at_infinity,
                use_ps_dists=use_ps_dists,
                use_sage_db=use_sage_db,
                progress_bar=progress_bar,
            )

            J = 1
            for i, emb in enumerate(emblist):
                fwrite(
                    "Computing %s-th period, attached to the embedding: %s"
                    % (i, Wlist[i].list()),
                    outfile,
                )
                tau, gtau, sign, limits = emb
                n_evals = sum((num_evals(t1, t2) for t1, t2 in limits))
                fwrite(
                    "Computing one period...(total of %s evaluations)" % n_evals,
                    outfile,
                )
                newJ = prod(
                    (double_integral_zero_infty(Phi, t1, t2) for t1, t2 in limits)
                ) ** ZZ(sign)
                Jlist.append(newJ)
                J *= newJ
    else:  # input_data is not None
        Phi, J = input_data[1:3]
    fwrite("Integral done. Now trying to recognize the point", outfile)
    fwrite("J_psi = %s" % J, outfile)
    fwrite("g belongs to %s" % J.parent(), outfile)
    # Try to recognize a generator
    if quaternionic:
        local_embedding = G.base_ring_local_embedding(working_prec)
    else:
        local_embedding = Qp(p, working_prec)
    mysterious_multiples = [1, 3, 5, 7, 9]
    twopowlist = [QQ(1) / 4, QQ(1) / 2, QQ(1), QQ(2), QQ(4)]
    twopowlist = [a * b for a, b in product(mysterious_multiples, twopowlist)]
    twopowlist = twopowlist + [o**-1 for o in twopowlist]
    twopowlist = sorted(list(set(twopowlist)))

    known_multiple = ZZ(nn * eisenstein_constant)
    while known_multiple % p == 0:
        known_multiple = ZZ(known_multiple / p)

    if not recognize_point:
        fwrite("known_multiple = %s" % known_multiple, outfile)
        if quit_when_done:
            magma.quit()
        return J, Jlist
    verbose(f"About to call recognize_J")
    verbose(f"known_multiple = {known_multiple}")
    verbose(f"twopowlist = {twopowlist}")
    candidate, twopow, J1 = recognize_J(
        E,
        J,
        K,
        local_embedding=local_embedding,
        known_multiple=known_multiple,
        twopowlist=twopowlist,
        prec=prec,
        outfile=outfile,
    )

    if candidate is not None:
        HCF = K.hilbert_class_field(names="r1") if hK > 1 else K
        if hK == 1:
            try:
                verbose("candidate = %s" % candidate)
                Ptsmall = E.change_ring(HCF)(candidate)
                fwrite("twopow = %s" % twopow, outfile)
                fwrite(
                    "Computed point:  %s * %s * %s" % (twopow, known_multiple, Ptsmall),
                    outfile,
                )
                fwrite("(first factor is not understood, second factor is)", outfile)
                fwrite(
                    "(r satisfies %s = 0)" % (Ptsmall[0].parent().gen().minpoly()),
                    outfile,
                )
                fwrite("================================================", outfile)
                if quit_when_done:
                    magma.quit()
                return Ptsmall
            except (TypeError, ValueError):
                verbose("Could not recognize the point.")
        else:
            verbose("candidate = %s" % candidate)
            fwrite("twopow = %s" % twopow, outfile)
            fwrite(
                "Computed point:  %s * %s * (x,y)" % (twopow, known_multiple), outfile
            )
            fwrite("(first factor is not understood, second factor is)", outfile)
            try:
                pols = [HCF(c).relative_minpoly() for c in candidate[:2]]
            except AttributeError:
                pols = [HCF(c).minpoly() for c in candidate[:2]]
            fwrite("Where x satisfies %s" % pols[0], outfile)
            fwrite("and y satisfies %s" % pols[1], outfile)
            fwrite("================================================", outfile)
            if quit_when_done:
                magma.quit()
            return candidate
    else:
        fwrite("================================================", outfile)
        if quit_when_done:
            magma.quit()
        return []
