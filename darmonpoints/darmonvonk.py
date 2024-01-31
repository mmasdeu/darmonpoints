from itertools import product

from sage.arith.misc import fundamental_discriminant
from sage.geometry.hyperbolic_space.hyperbolic_interface import HyperbolicPlane
from sage.modular.pollack_stevens.manin_map import *

from darmonpoints.arithgroup import angle_sign, intersect_geodesic_arcs
from darmonpoints.cohomology_arithmetic import ArithAction, CohArbitrary
from darmonpoints.homology import *
from darmonpoints.ocmodule import AddMeromorphicFunctions
from darmonpoints.sarithgroup import *
from darmonpoints.util import *

distinguished_open = "OCp"  # Needed if we want to compare with Darmon points!
# distinguished_open = 'Uinf'


class OverconvergentDVCocycle(SageObject):
    def __init__(self, G, phi0, base_ring=None):
        self.G = G
        self.phi0 = phi0
        HDiv = phi0.parent()
        Div = HDiv.coefficient_module()
        if base_ring is None:
            K = Div.base_ring()
        else:
            K = base_ring
        self.K = K
        prec = K.precision_cap()
        wp = G.embed(G.wp(), prec)
        act = lambda g, v: g.matrix().change_ring(K) * v

        if distinguished_open == "Uinf":
            Mer = AddMeromorphicFunctions(K)
        else:
            Mer = AddMeromorphicFunctions(
                K, twisting_matrix=Matrix(ZZ, 2, 2, [0, 1, G.prime(), 0])
            )  # DEBUG: used to be wp
        self.HpMer = CohArbitrary(G.small_group(), Mer, action_map=act)
        Gpgens = G.small_group().gens()
        phi = self.HpMer([phi0.evaluate(G.Gpn(g.quaternion_rep)) for g in Gpgens])
        phi_tw = self.HpMer(
            [
                phi0.evaluate(
                    G.Gpn(G.wp() ** -1 * g.quaternion_rep * G.wp())
                ).left_act_by_matrix(wp)
                for g in Gpgens
            ]
        )
        if distinguished_open == "Uinf":
            self.phi1 = phi_tw
            self.phi2 = phi
        else:
            self.phi1 = phi
            self.phi2 = phi_tw

    def base_ring(self):
        return self.K

    def _str_(self):
        return "Overconvergent DV cocycle for group %s" % self.G

    def improve(self, prec):
        G = self.G
        p = G.prime()
        GGp = G.small_group()
        if distinguished_open == "Uinf":
            Up_reps = tuple([G.wp() ** -1 * o * G.wp() for o in G.get_Up_reps()])
        else:
            Up_reps = tuple(G.get_Up_reps())
        Up_data = GGp.get_hecke_data(p, hecke_reps=Up_reps)
        tmp = self.HpMer(self.phi1)
        phi_list = [self.HpMer(0), self.HpMer(self.phi1)]
        val = -1
        for i in range(prec):
            update_progress(
                float(val + 1) / prec, "Iterating Up (%s/%s)" % (val + 1, prec)
            )
            tmp = self.HpMer.apply_hecke_operator(
                tmp, p, hecke_data=Up_data, hecke_reps=Up_reps, as_Up=True
            )
            phi_list[i % 2] += tmp
            val = min([o.valuation() for o in tmp.values()])
            if val >= prec:
                break
        self.phi_even, self.phi_odd = phi_list
        return

    def evaluate_at_cycle(self, theta, parity):
        ans_even, ans_odd = self._evaluate_at_cycle(theta)
        if parity == "even":
            return ans_even
        elif parity == "odd":
            return ans_odd
        elif parity == "+":
            return ans_even - ans_odd
        elif parity == "-":
            return ans_even + ans_odd

    def _evaluate_at_cycle(self, theta):
        p = self.G.prime()
        ans_odd = 0
        ans_even = 0
        for g, D in theta:
            ans_odd += self.phi_odd.evaluate(g).evaluate_additive(D)
            ans_even += self.phi_even.evaluate(g).evaluate_additive(D)
        return ans_even, ans_odd


def construct_conjectural_field(
    D1,
    D2,
    magma,
    extra_conductor_1=1,
    extra_conductor_2=1,
    base=None,
    return_units=True,
):
    if base is None:
        try:
            _ = QQ(D1)
            _ = QQ(D2)
            base = QQ
        except TypeError:
            base = D1.parent()
    R = PolynomialRing(QQ, "x")
    x = R.gen()
    F1 = (
        base.extension(x**2 - D1, names="aaa")
        if base != QQ
        else QuadraticField(D1, names="aaa")
    )
    F2 = (
        base.extension(x**2 - D2, names="bbb")
        if base != QQ
        else QuadraticField(D2, names="aaa")
    )
    F1 = F1.absolute_field(names="aaa")
    F2 = F2.absolute_field(names="bbb")

    magma.eval(
        "_, m := RayClassGroup(%s * MaximalOrder(%s), %s)"
        % (
            extra_conductor_1,
            magma(F1).name(),
            str(list(range(1, len(F1.real_embeddings()) + 1))),
        )
    )
    fF1 = R(
        sage_eval(
            magma.eval(
                "ElementToSequence(DefiningPolynomial(AbsoluteField(NumberField(AbelianExtension(m)))))"
            )
        )
    )
    H1 = NumberField(sage_eval(str(gp.polredabs(fF1)), locals={"x": x}), names="a")
    a = H1.gen()

    magma.eval(
        "_, m := RayClassGroup(%s * MaximalOrder(%s), %s)"
        % (
            extra_conductor_2,
            magma(F2).name(),
            str(list(range(1, len(F2.real_embeddings()) + 1))),
        )
    )
    fF2 = R(
        sage_eval(
            magma.eval(
                "ElementToSequence(DefiningPolynomial(AbsoluteField(NumberField(AbelianExtension(m)))))"
            )
        )
    )
    H2 = NumberField(sage_eval(str(gp.polredabs(fF2)), locals={"x": x}), names="b")
    b = H2.gen()
    M = NumberField(
        sage_eval(
            str(gp.polredabs(H1.composite_fields(H2)[0].polynomial())), locals={"x": x}
        ),
        names="z",
    )
    phi1, phi2 = F1.embeddings(M)[0], F2.embeddings(M)[0]
    if return_units:
        return M, list(
            set([phi1(o) for o in F1.units()] + [phi2(o) for o in F2.units()])
        )
    else:
        return M


# If ringclassfield = False, only construct the compositum of the quadratic fields
def construct_bigfield(Dlist, magma, base=None, ringclassfield=True):
    if base is None:
        base = QQ
    R = PolynomialRing(QQ, "x")
    x = R.gen()
    Hlist = []
    for D in Dlist:
        F1 = base.extension(x**2 - D, names="a") if base != QQ else QuadraticField(D)
        F1 = F1.absolute_field(names="a")
        if ringclassfield:
            magma.eval(
                "_, m := RayClassGroup(%s * MaximalOrder(%s), %s)"
                % (
                    1,
                    magma(F1).name(),
                    str(list(range(1, len(F1.real_embeddings()) + 1))),
                )
            )
            fF1 = R(
                sage_eval(
                    magma.eval(
                        "ElementToSequence(DefiningPolynomial(AbsoluteField(NumberField(AbelianExtension(m)))))"
                    )
                )
            )
            H1 = NumberField(fF1, names="a")
            a = H1.gen()
        else:
            H1 = F1
        Hlist.append(H1)

    H = Hlist[0]
    for H2 in Hlist[1:]:
        H = NumberField(
            sage_eval(
                str(gp.polredabs(H.composite_fields(H2)[0].polynomial())),
                locals={"x": x},
            ),
            names="z",
        )
    return H


def darmon_vonk_overconvergent_cocycle(
    G, D, prec, lift=True, working_prec=None, extra_conductor=1, outfile=None, **kwargs
):
    fwrite("# Initializing cocycle...", outfile)
    phi0 = darmon_vonk_cocycle(
        G, D, prec, extra_conductor=extra_conductor, outfile=outfile, **kwargs
    )
    Phi = OverconvergentDVCocycle(G, phi0)
    if lift:
        fwrite("# Lifting cocycle...", outfile)
        Phi.improve(prec)
    return Phi


def darmon_vonk_group(p, DB, outfile=None, **kwargs):
    magma = kwargs.pop("magma", None)
    additional_level = kwargs.pop("additional_level", 1)
    if magma is None:
        from sage.interfaces.magma import Magma

        magma = Magma()
    grouptype = kwargs.pop("grouptype", "PSL2")
    try:
        _ = ZZ(p)
        base = QQ
    except TypeError:
        base = p.number_field()
    return BigArithGroup(
        p,
        DB,
        additional_level,
        base=base,
        grouptype=grouptype,
        cohomological=True,
        use_shapiro=False,
        magma=magma,
        outfile=outfile,
        **kwargs,
    )  # DEBUG: wish could put PGL2 (sometimes it works, and it's much faster)


def darmon_vonk_point(
    p,
    DB,
    D1,
    D2,
    prec,
    working_prec=None,
    magma=None,
    extra_conductor_1=1,
    extra_conductor_2=1,
    recognize_point="algdep",
    parity="all",
    degree_bound=8,
    outfile=None,
    **kwargs,
):
    r"""
    EXAMPLES ::

    sage: from darmonpoints.darmonvonk import darmon_vonk_point
    sage: J = darmon_vonk_point(5, 1, 3, 13, 60, parity='+', recognize_point='algdep',magma=magma) # optional - magma
    #### Starting computation of the Darmon-Vonk point ####
    ...
    f = 7*x^2 + 11*x + 7
    """
    if magma is None:
        from sage.interfaces.magma import Magma

        magma = Magma()
    if recognize_point not in ["algdep", "lindep", "all", "none"]:
        raise ValueError(
            "recognize_point (= '%s' ) should be one of 'algdep', 'lindep', 'all' or 'none'"
            % str(recognize_point)
        )
    if parity not in ["+", "-", "even", "odd", "all"]:
        raise ValueError("Parity should be one of '+', '-', 'even', 'odd' or 'all'")
    if outfile == "log":
        outfile = "%s_%s_%s-%s_%s-%s_%s_%s.log" % (
            p,
            DB,
            D1,
            extra_conductor_1,
            D2,
            extra_conductor_2,
            prec,
            datetime.datetime.now().strftime("%Y%m%d-%H%M%S"),
        )
        outfile = outfile.replace("/", "div")
        outfile = "/tmp/darmonvonkpoint_" + outfile
    if working_prec is None:
        working_prec = prec

    max_degree = kwargs.get("max_degree", 16)

    fwrite("#### Starting computation of the Darmon-Vonk point ####", outfile)
    magma_seed = kwargs.get("magma_seed", None)
    if magma_seed is not None:
        fwrite("# magma_seed is set to %s" % magma_seed, outfile)
    else:
        magma_seed = ZZ.random_element(100000)
        fwrite("# magma_seed will be set to %s" % magma_seed, outfile)
        kwargs["magma_seed"] = magma_seed
    try:
        p = ZZ(p)
        fwrite("# F = Q", outfile)
    except TypeError:
        pass
    try:
        F = p.number_field()
        fwrite("# F = NumberField({fmin})".format(fmin=F.polynomial()), outfile)
    except AttributeError:
        F = QQ
    if working_prec is None:
        working_prec = max([2 * prec + 10, 30])
    fwrite("# D_B = %s" % str(DB), outfile)
    fwrite("# D1|conductor = %s|%s" % (D1, extra_conductor_1), outfile)
    fwrite(
        "# Calculation with p = %s and prec = %s (working_prec = %s)"
        % (p, prec, working_prec),
        outfile,
    )
    if outfile is not None:
        print("Partial results will be saved in %s" % outfile)

    Phi = kwargs.get("cocycle", None)
    if Phi is None:
        max_tries = kwargs.pop("max_tries", 10)
        ntries = 0
        while ntries < max_tries:
            try:
                G = kwargs.pop("G", None)
                if G is None:
                    fwrite("# Initializing S-arithmetic group...", outfile)
                    G = darmon_vonk_group(p, DB, magma=magma, outfile=None, **kwargs)
                G.get_embedding(2 * prec)
                Phi = darmon_vonk_overconvergent_cocycle(
                    G,
                    D1,
                    prec,
                    lift=False,
                    extra_conductor=extra_conductor_1,
                    outfile=outfile,
                    **kwargs,
                )
                needs_lift = True
                break
            except RuntimeError as e:
                print("Runtime Error during calculation of overconvergent cocycle")
                print("Error: ", e)
                return []
            except (AssertionError, TypeError) as e:
                print("Assertion or Type Error:", e)
                ntries += 1
                print(f"NTRIES = {ntries} !!!!!")
                print("")
                continue
        if ntries == max_tries:
            print("Reached maximum number of tries")
            return []

    else:
        G = Phi.G
        kwargs.pop("G", None)  # Discard extra parameter G
        needs_lift = False

    if type(D2) is list:
        D2_list = D2
    else:
        D2_list = [D2]
    if type(extra_conductor_2) is list:
        extra_conductor_2_list = extra_conductor_2
    else:
        extra_conductor_2_list = [extra_conductor_2]

    K = Phi.phi0.parent().coefficient_module().base_ring()
    cycle_list = []
    for D2, extra_conductor_2 in product(D2_list, extra_conductor_2_list):
        if D2 == D1 and extra_conductor_2 == extra_conductor_1:
            fwrite(
                "# skipping pair (%s, %s) because it coincides with cocycle"
                % (D2, extra_conductor_2),
                outfile,
            )
            continue
        fwrite("# Initializing cycle...", outfile)
        fwrite("#  D2|conductor = %s|%s" % (D2, extra_conductor_2), outfile)
        try:
            theta0, factor = darmon_vonk_cycle(
                G,
                D2,
                working_prec,
                extra_conductor=extra_conductor_2,
                padic_field=K,
                outfile=outfile,
                **kwargs,
            )
            fwrite("#  Factor = %s" % factor, outfile)
            cycle_list.append((D2, extra_conductor_2, theta0, factor))
        except (ValueError, NotImplementedError, RuntimeError) as e:
            fwrite('Skipping because of "%s"' % str(e), outfile)
            continue
    if needs_lift:
        fwrite("# Lifting cocycle...", outfile)
        Phi.improve(prec)

    if parity == "all":
        parity_list = ["+", "-", "even", "odd"]
    else:
        parity_list = [parity]
    ans_list = kwargs.get("result_list", None)
    if ans_list is None:
        ans_list = []
    scaling = kwargs.get("scaling", 1)
    for D2, extra_conductor_2, theta0, factor in cycle_list:
        theta = trace_cycle(G, theta0, twist=False)
        fwrite(35 * "#", outfile)
        fwrite(
            '# Integrating (%s|%s) and parity "%s"' % (D2, extra_conductor_2, parity),
            outfile,
        )
        fwrite(35 * "-", outfile)
        try:
            Jeven, Jodd = Phi._evaluate_at_cycle(theta)
            J0 = Phi.phi0.pair_with_cycle(theta0)
        except ValueError as e:
            print("Found error while integrating (%s). Skipping..." % e)
            continue
        for parity in parity_list:
            if parity == "even":
                J = Jeven
            elif parity == "odd":
                J = Jodd
            elif parity == "+":
                J = Jeven - Jodd
            elif parity == "-":
                J = Jeven + Jodd
            if parity != "odd":
                J += J0
            print(f"factor = {factor}, scaling = {scaling}")
            J = (J / (factor * scaling)).exp().add_bigoh(prec)
            try:
                p = ZZ(p)
                fwrite("F = QQ", outfile)
            except TypeError:
                pass
            try:
                F = p.number_field()
                fwrite(
                    "F.<{r}> = NumberField({fmin})".format(
                        r=F.gen(), fmin=F.polynomial()
                    ),
                    outfile,
                )
            except AttributeError:
                F = QQ
            fwrite(
                "K.<{g}> = Qp({p}, {prec}).extension({defpoly})".format(
                    g=K._names[0],
                    p=K.prime(),
                    prec=K.precision_cap(),
                    defpoly=K.defining_polynomial(exact=True),
                ),
                outfile,
            )
            fwrite("J = %s" % J, outfile)
            fwrite("# Norm(J) = %s" % J.norm(), outfile)
            recog_data = []
            Ftriv = construct_bigfield([D1, D2], magma, base=F, ringclassfield=False)
            if recognize_point in ["algdep", "all"]:
                for degree in range(2, degree_bound + 1):
                    Jg, ff = recognize_DV_algdep(J, degree, outfile=outfile)
                    if Jg is not None:
                        recog_data.append((Jg, ff))
                        break
            if recognize_point in ["lindep", "all"]:
                try:
                    print("Constructing field of definition...")
                    M = kwargs.get("field_of_definition", None)
                    if M is None:
                        M = construct_conjectural_field(
                            D1,
                            D2,
                            magma,
                            extra_conductor_1,
                            extra_conductor_2,
                            return_units=False,
                        )
                    fwrite(
                        "# Conjectured field of definition generated by polynomial %s"
                        % M.defining_polynomial(),
                        outfile,
                    )
                    if M.degree() > max_degree:
                        fwrite(
                            "# Too large for lindep (max_degree = %s), skipping."
                            % max_degree,
                            outfile,
                        )
                    else:
                        units = kwargs.get("allowed_units", None)
                        prime_list = kwargs.get(
                            "allowed_primes",
                            prime_list_candidates(
                                D1, D2, extra_conductor_1, extra_conductor_2
                            ),
                        )
                        fwrite("# Prime list = %s" % prime_list, outfile)
                        ans = recognize_DV_lindep(
                            J, M, prime_list, units=units, outfile=outfile, **kwargs
                        )
                        if ans is not None:
                            recog_data.append(ans)
                except KeyboardInterrupt:
                    "Recognition interrupted..."
            if len(recog_data) == 0:
                ans_list.append(
                    (
                        J,
                        None,
                        parity,
                        D1,
                        extra_conductor_1,
                        D2,
                        extra_conductor_2,
                        Ftriv,
                    )
                )
            elif len(recog_data) == 1:
                ans_list.append(
                    (
                        J,
                        recog_data[0],
                        parity,
                        D1,
                        extra_conductor_1,
                        D2,
                        extra_conductor_2,
                        Ftriv,
                    )
                )
            else:
                ans_list.append(
                    (
                        J,
                        recog_data,
                        parity,
                        D1,
                        extra_conductor_1,
                        D2,
                        extra_conductor_2,
                        Ftriv,
                    )
                )
    return ans_list


def admissible_discriminants(p, D, bound, magma=None):
    if magma is None:
        from sage.interfaces.magma import Magma

        magma = Magma()
    ans = []
    try:
        F = p.number_field()
        x = F["x"].gen()
        a, b = D
        u0 = F.units()[0]
        for n0, u in product(
            [1, -1, u0, -u0],
            sum([F.elements_of_norm(nZ) for nZ in range(2, bound)], []),
        ):
            n = n0 * u
            try:
                K = F.extension(x**2 - n, names="z")
                z = K.gen()
            except ValueError:
                continue
            B = magma.QuaternionAlgebra(magma(F), magma(a), magma(b))
            Km = magma(K)
            if magma.eval(f"HasEmbedding({Km.name()}, {B.name()})")[:5] == "true":
                if len(K.units()) > len(F.units()):
                    ans.append(n)
    except AttributeError:
        F = QQ
        facts = [o[0] for o in ZZ(D).factor()] + [ZZ(p)]
        for n in range(1, bound):
            if n != fundamental_discriminant(n):
                continue
            if all(kronecker_symbol(n, ell) in [-1, 0] for ell in facts) and n % p != 0:
                ans.append(n)
    return ans


def darmon_vonk_cocycle(
    G,
    D,
    prec,
    extra_conductor=1,
    padic_field=None,
    hecke_data=None,
    outfile=None,
    **kwargs,
):
    ## To define the cocycle
    scaling = kwargs.get("scaling", 1)
    GG = G.large_group()
    GGp = G.small_group()
    F_to_Qp = G.base_ring_local_embedding(prec)
    p = G.prime()
    base_point = kwargs.get("base_point", None)
    if base_point is None:
        base_point = ComplexField(100)(0.8312, 1.3621)
    elif base_point == "random":
        base_point = ComplexField(100).random_element(2)
        if base_point.imag() < 0:
            base_point = base_point.conjugate()
    gamma_tau, tau_p = GG.embed_order(
        p,
        D,
        prec,
        extra_conductor=extra_conductor,
        outfile=outfile,
        F_to_Qp=F_to_Qp,
        padic_field=padic_field,
        **kwargs,
    )
    K = tau_p.parent()
    V = Divisors(K)
    f = lambda g, v: g.matrix().change_ring(K) * v
    HDiv = CohArbitrary(GG, V, action_map=f)
    HpDiv = CohArbitrary(GGp, V, action_map=f)

    DVCoh = DVCocycle(GG, base_point, gamma_tau, tau_p)
    phi0 = HDiv(DVCoh)

    if scaling != 1:
        phi0 *= scaling

    assert phi0.check_cocycle_property(), "Cocycle property not satisfied!"

    if hecke_data is not None:
        q, pol = hecke_data
        pol = QQ["x"](pol)
        phi0 = HDiv.act_by_poly_hecke(phi0, q, pol)

    if not all(o.degree() == 0 for o in phi0.values()):
        raise ValueError(
            "Not zero-degree-valued: %s" % (str([o.degree() for o in phi0.values()]))
        )
    return phi0


def darmon_vonk_cycle(
    G,
    D,
    prec,
    extra_conductor=1,
    padic_field=None,
    hecke_data=None,
    outfile=None,
    **kwargs,
):
    p = G.prime()
    F_to_Qp = G.base_ring_local_embedding(prec)
    scaling = kwargs.get("scaling", 1)
    GG = G.large_group()
    Gp = G.small_group()
    F = G.F
    gamma_zeta, zeta = GG.embed_order(
        p,
        D,
        prec,
        F_to_Qp=F_to_Qp,
        padic_field=padic_field,
        extra_conductor=extra_conductor,
        outfile=outfile,
        **kwargs,
    )
    conjugate = kwargs.get("conjugate", False)
    if conjugate:
        zeta = zeta.trace() - zeta
    K = zeta.parent()
    Div = Divisors(K)
    H1 = OneChains(GG, Div)
    compute_degree_zero = kwargs.pop("compute_degree_zero", True)
    if compute_degree_zero:
        D1 = Div(zeta)
    else:
        D1 = Div(zeta) - Div(zeta.trace() - zeta)
    ans0 = H1({GG(gamma_zeta): D1})
    assert ans0.is_cycle(), "We expected to get a cycle!"
    if hecke_data is not None:
        q, pol = hecke_data
        pol = QQ["x"](pol)
        ans0 = ans0.act_by_poly_hecke(q, pol)

    if scaling != 1:
        ans0 = ans0.mult_by(scaling)

    if compute_degree_zero:
        theta, mult = ans0.zero_degree_equivalent(allow_multiple=True)
    else:
        theta, mult = ans0, 1
    return theta, mult * scaling


def trace_cycle(G, theta, twist=False):
    Div = theta.parent().coefficient_module()
    K = Div.base_ring()
    prec = K.precision_cap()
    Gp = G.small_group()
    HpDiv = OneChains(Gp, Div)
    wpmat = G.embed(G.wp(), prec).change_ring(K)
    theta1 = HpDiv({})
    if (distinguished_open == "Uinf") == twist:  # DEBUG - this is awful
        for gamma, D in theta:
            for _, h in G.get_covering(1):
                hg = Gp(
                    G.reduce_in_amalgam(
                        h * gamma.conjugate_by(G.wp() ** -1).quaternion_rep
                    )
                )
                theta1 += HpDiv({hg: Gp(h) * (wpmat * D)})
    else:
        for gamma, D in theta:
            for h in G.get_BT_reps():
                hg = Gp(G.reduce_in_amalgam(h * gamma.quaternion_rep))
                theta1 += HpDiv({hg: Gp(h) * D})
    return theta1


class DVCocycle(SageObject):
    def __init__(self, G, x0, gamma_tau, tau_p):
        self._G = G
        self._x0 = x0
        K = tau_p.parent()
        prec = K.precision_cap()
        CC = x0.parent()
        vinf = G.get_archimedean_embedding(CC.precision())

        gtau_quat = gamma_tau.quaternion_rep
        if hasattr(gtau_quat, "nrows"):
            trd, nrd = gtau_quat.trace(), gtau_quat.determinant()
        else:
            trd, nrd = gtau_quat.reduced_trace(), gtau_quat.reduced_norm()
        aa, bb, cc, dd = vinf(gtau_quat).list()
        try:
            F_to_R = trd.parent().real_embeddings(CC.precision())[
                0
            ]  # DEBUG: hard coded first embedding
        except AttributeError:
            F_to_R = lambda x: CC(0).real().parent()(x)
        if cc == 0:
            assert bb == 0, "Expected diagonal matrix but it is not: bb = %s" % bb
            self._tau_inf = aa.parent()(0)
            self._tau_inf_bar = Infinity
            self._t0 = 5 * CC.gen()
        else:
            self._tau_inf = (aa - dd + F_to_R(trd**2 - 4 * nrd).sqrt()) / (2 * cc)
            self._tau_inf_bar = (aa - dd - F_to_R(trd**2 - 4 * nrd).sqrt()) / (2 * cc)
            t0 = intersect_geodesic_arcs(
                self._tau_inf,
                self._tau_inf_bar,
                Infinity,
                ZZ(65) / 101 * self._tau_inf + ZZ(36) / 101 * self._tau_inf_bar,
            )
            assert t0 is not None, "Could not find intersection!"
            self._t0 = t0

        self._tau = tau_p
        tau = self._tau
        tau_bar = tau.trace() - tau
        self._gamma_tau = gamma_tau

        action_map = lambda g, x: act_flt(vinf(g.quaternion_rep), x)
        action = ArithAction(G, CC, action_map)
        CC._unset_coercions_used()
        CC.register_action(action)

        action_map = lambda g, x: act_flt(G.get_embedding(prec)(g.quaternion_rep), x)
        action = ArithAction(G, K, action_map)
        K._unset_coercions_used()
        K.register_action(action)

    def all_matrix_candidates(self, gamma):
        r"""
        Returns a list S of matrices in G satisfying
        g * (x1, gamma1*x1) meets (x2, gamma2*x2) => g belongs to S.
        """
        x0 = self._x0
        gamma1 = self._gamma_tau
        x1 = self._t0
        m1 = list(set(self._G.mat_list(x0, self._G(gamma) * x0, check_fundom=True)))
        m2 = list(set(self._G.mat_list(x1, self._G(gamma1) * x1, check_fundom=True)))
        ans = [g1 * g2**-1 for g1, g2 in product(m1, m2)]
        return [self._G(o) for o in list(set(ans))]

    def evaluate(self, gamma):
        HH = HyperbolicPlane().UHP()
        Div = Divisors(self._tau.parent())
        if gamma.quaternion_rep == 1 or gamma.quaternion_rep == -1:
            return Div(0)
        wlist = set([])
        x0 = self._x0
        gamma_of_x0 = gamma * x0
        tau = x0.parent()(self._tau_inf)
        tau_bar = x0.parent()(self._tau_inf_bar)
        ans = Div(0)
        for g in self.all_matrix_candidates(gamma):
            c1 = HH.get_geodesic(x0, gamma_of_x0)
            gtau = g * tau
            gtau_bar = g * tau_bar
            c2 = HH.get_geodesic(gtau, gtau_bar)
            if intersect_geodesic_arcs(x0, gamma_of_x0, gtau, gtau_bar) is not None:
                ans += angle_sign(c1, c2) * (g * Div(self._tau))
        return Div([(n.sign(), P) for P, n in ans])


def prime_list_candidates(D1, D2, extra_conductor_1=1, extra_conductor_2=1):
    prime_list = set([])
    try:
        D1 = D1.norm().abs()
        D2 = D2.norm().abs()
        D1D2 = D1 * D2
    except AttributeError:
        D1D2 = (
            fundamental_discriminant(D1)
            * fundamental_discriminant(D2)
            * extra_conductor_1**2
            * extra_conductor_2**2
        )
    for x in range(RR(D1D2).sqrt().ceil()):
        res = D1D2 - x * x
        if res % 4 == 0:
            for p, _ in (res // 4).factor():
                if kronecker_symbol(D1, p) != 1 and kronecker_symbol(D2, p) != 1:
                    prime_list.add(p)
    return sorted(list(prime_list))
