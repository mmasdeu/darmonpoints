######################
##                  ##
##    QUATERNIONIC  ##
##    ARITHMETIC    ##
##    GROUP         ##
##                  ##
######################
from collections import defaultdict
from itertools import chain, groupby, islice, product, starmap, tee
from os.path import dirname

from sage.algebras.quatalg.all import QuaternionAlgebra
from sage.functions.trig import arctan
from sage.groups.group import AlgebraicGroup
from sage.matrix.all import Matrix, matrix
from sage.misc.all import cached_method, lazy_attribute, walltime
from sage.misc.misc_c import prod
from sage.misc.persist import db
from sage.misc.verbose import verbose
from sage.modular.arithgroup.congroup_gamma0 import Gamma0_constructor as Gamma0
from sage.modular.btquotients.btquotient import BruhatTitsTree
from sage.modular.cusps import Cusp
from sage.modules.all import vector
from sage.modules.free_module import FreeModule_generic
from sage.rings.all import (
    QQ,
    RR,
    ZZ,
    ComplexField,
    NumberField,
    PolynomialRing,
    Qp,
    Qq,
    QuadraticField,
    RealField,
    Zmod,
)
from sage.structure.element import MultiplicativeGroupElement
from sage.structure.parent import Parent
from sage.structure.sage_object import SageObject, load, save

from .arithgroup import (
    ArithGroup_nf_fuchsian,
    ArithGroup_nf_kleinian,
    ArithGroup_nf_matrix,
    ArithGroup_nf_matrix_new,
    ArithGroup_rationalmatrix,
    ArithGroup_rationalquaternion,
)
from .homology_abstract import ArithHomology, HomologyGroup
from .representations import TrivialAction
from .util import *


class BTEdge(SageObject):
    r"""
    A BTEdge is represented by an element `gamma`, and then a flag called `reverse`.
    The flag reverse indicates whether we refer to the opposite edge of the one
    represented by `gamma`.
    """

    def __init__(self, reverse, gamma):
        self.reverse = reverse
        self.gamma = gamma
        set_immutable(self.gamma)

    def _repr_(self):
        return "(%s)^%s" % (self.gamma, "+" if self.reverse == False else "-")

    def __iter__(self):
        return iter([self.reverse, self.gamma])


def attach_kleinian_code(magma):
    page_path = dirname(__file__) + "/KleinianGroups-1.0/klngpspec"
    magma.attach_spec(page_path)
    magma.eval("Page_initialized := true")
    return


def is_page_initialized(magma):
    try:
        return magma.eval("Page_initialized") == "true"
    except RuntimeError:
        return False


def BigArithGroup(
    p,
    quat_data,
    level,
    base=None,
    grouptype=None,
    seed=None,
    use_sage_db=False,
    magma=None,
    logfile=None,
    **kwargs,
):
    if magma is None:
        try:
            from sage.interfaces.magma import Magma

            magma = Magma(logfile=logfile)
        except RuntimeError:
            print("Could not initialize Magma. Continue at your own risk!")
            pass
    try:
        if seed is not None:
            magma.eval("SetSeed(%s)" % seed)
        if not is_page_initialized(magma):
            attach_kleinian_code(magma)
        if logfile is not None:
            magma.eval('SetVerbose("Kleinian",2)')
    except RuntimeError:
        pass
    a, b = None, None
    try:
        discriminant = ZZ(quat_data)
        if base is not None:
            assert base == QQ
        else:
            base = QQ
        fname = "arithgroup%s_%s_%s_%s.sobj" % (
            seed,
            p,
            discriminant,
            level,
        )  # Fix this name
    except TypeError:
        a, b = quat_data
        if base is None:
            base = a.parent()
        discriminant = QuaternionAlgebra(base, a, b).discriminant()
        fname = "arithgroup%s_%s_%s_%s.sobj" % (
            seed,
            p,
            discriminant,
            level,
        )  # Fix this name
    if base != QQ:
        use_sage_db = False  # This is not implemented yet

    if grouptype is None:
        if base == QQ:
            grouptype = "PSL2"
        else:
            grouptype = "PSL2"  # DEBUG, was PGL2

    if use_sage_db:
        try:
            newobj = db(fname)
        except OSError:
            verbose("Group not found in database. Computing from scratch.")
            newobj = BigArithGroup_class(
                base,
                p,
                discriminant,
                level,
                seed,
                grouptype=grouptype,
                magma=magma,
                **kwargs,
            )
            newobj.save_to_db()
    else:
        if a is not None:
            newobj = BigArithGroup_class(
                base,
                p,
                discriminant,
                abtuple=(a, b),
                level=level,
                seed=seed,
                grouptype=grouptype,
                magma=magma,
                **kwargs,
            )
        else:
            newobj = BigArithGroup_class(
                base,
                p,
                discriminant,
                level=level,
                seed=seed,
                grouptype=grouptype,
                magma=magma,
                **kwargs,
            )
    return newobj


class BigArithGroup_class(AlgebraicGroup):
    r"""
    This class holds information about the group `\Gamma`: a finite
    presentation for it, a solution to the word problem,...

    Initializes the group attached to a `\ZZ[1/p]`-order of the rational quaternion algebra of
    discriminant `discriminant` and  level `n`.

    TESTS:

        sage: from darmonpoints.sarithgroup import BigArithGroup
        sage: GS = BigArithGroup(7,6,1,outfile='/tmp/darmonpoints.tmp',use_shapiro=False) #  optional - magma
        sage: G = GS.small_group() #  optional - magma
        sage: a = G([2,2,1,1,1,-3]) #  optional - magma
        sage: b = G([2,2,2])    #  optional - magma
        sage: c = G([3])        #  optional - magma
        sage: print(a * b) # random #  optional - magma
        -236836769/2 + 120098645/2*i - 80061609/2*j - 80063439/2*k
        sage: b.quaternion_rep # random #  optional - magma
        846 - 429*i + 286*j + 286*k
    """

    def __init__(
        self,
        base,
        p,
        discriminant,
        abtuple=None,
        level=1,
        outfile=None,
        magma=None,
        character=None,
        **kwargs,
    ):
        seed = kwargs.get("seed", None)
        self.seed = seed
        self.magma = magma
        self._use_shapiro = kwargs.get("use_shapiro", False)
        self._hardcode_matrices = kwargs.get(
            "hardcode_matrices", False
        )  # ((abtuple is None and discriminant == 1) or abtuple == (1,1)))
        nscartan = kwargs.get("nscartan", None)
        if seed is not None:
            verbose("Setting Magma seed to %s" % seed)
            self.magma.eval("SetSeed(%s)" % seed)
        self.F = base
        if self.F != QQ:
            Fideal = self.F.maximal_order().ideal
            self.ideal_p = Fideal(p)
            self.norm_p = ZZ(p.norm())
            self.discriminant = Fideal(discriminant)
            self.level = Fideal(level)
        else:
            Fideal = ZZ
            self.ideal_p = ZZ(p)
            self.norm_p = ZZ(p)
            self.discriminant = ZZ(discriminant)
            self.level = ZZ(level)

        if nscartan is not None:
            self.level *= nscartan

        if self._hardcode_matrices:
            assert abtuple is None and self.discriminant == 1 or abtuple == (1, 1)

        self.p = self.norm_p.prime_divisors()[0]
        if not self.ideal_p.is_prime():
            raise ValueError("p (=%s) must be prime" % self.p)

        if self._use_shapiro:
            covol = covolume(self.F, self.discriminant, self.level)
        else:
            covol = covolume(self.F, self.discriminant, self.ideal_p * self.level)
        verbose("Estimated Covolume = %s" % covol)
        difficulty = covol**2
        verbose("Estimated Difficulty = %s" % difficulty)

        info_magma = kwargs.pop("info_magma", None)
        verbose("Initializing arithmetic group G(pn)...")
        kwargs["O_magma"] = kwargs.pop("GpnBasis", None)
        t = walltime()
        lev = self.ideal_p * self.level
        if character is not None:
            lev = [lev, character]
        self.Gpn = kwargs.get("Gpn", None)
        if self.Gpn is None:
            self.Gpn = ArithGroup(
                self.F,
                self.discriminant,
                abtuple,
                lev,
                info_magma=info_magma,
                magma=magma,
                compute_presentation=not self._use_shapiro,
                **kwargs,
            )
        self.Gpn.get_embedding = self.get_embedding
        self.Gpn.embed = self.embed

        verbose("Initializing arithmetic group G(n)...")
        q = kwargs.get("extra_q", 1)
        self.ideal_q = Fideal(q)
        lev = self.ideal_q * self.level
        if character is not None:
            lev = [lev, character]
        kwargs["O_magma"] = kwargs.pop("GnBasis", None)
        self.Gn = kwargs.get("Gn", None)
        if self.Gn is None:
            if info_magma is None:
                info_magma = self.Gpn
            self.Gn = ArithGroup(
                self.F,
                self.discriminant,
                abtuple,
                lev,
                info_magma=info_magma,
                magma=magma,
                compute_presentation=True,
                **kwargs,
            )
        t = walltime(t)
        verbose("Time for calculation T = %s" % t)
        verbose("T = %s x difficulty" % RealField(25)(t / difficulty))
        self.Gn.embed = self.embed
        self.Gn.get_embedding = self.get_embedding

        if hasattr(self.Gpn.B, "is_division_algebra"):
            fwrite(
                "# B = F<i,j,k>, with i^2 = %s and j^2 = %s"
                % (self.Gpn.B.gens()[0] ** 2, self.Gpn.B.gens()[1] ** 2),
                outfile,
            )
            fwrite("# disc(B) = %s" % self.Gpn.B.discriminant(), outfile)
        else:
            fwrite("# B = M_2(F)", outfile)
        self._prec = -1
        iotap = self.get_embedding(200)
        fwrite(
            "# Local embedding B to M_2(Q_p) sends i to %s and j to %s"
            % (
                iotap(self.Gn.B.gen(0)).apply_map(lambda o: o.add_bigoh(5)).list(),
                iotap(self.Gn.B.gen(1)).apply_map(lambda o: o.add_bigoh(5)).list(),
            ),
            outfile,
        )
        try:
            basis_data_1 = list(self.Gn.Obasis)
            if not self.use_shapiro():
                basis_data_p = list(self.Gpn.Obasis)
        except AttributeError:
            try:
                basis_data_1 = self.Gn._get_basis_invmat().inverse().columns()
                if not self.use_shapiro():
                    basis_data_p = self.Gpn._get_basis_invmat().inverse().columns()
            except AttributeError:
                basis_data_1 = "?"
                basis_data_p = "?"
        fwrite("# R with basis %s" % basis_data_1, outfile)
        self.Gn.get_Up_reps = self.get_Up_reps
        if not self.use_shapiro():
            fwrite("# R(p) with basis %s" % basis_data_p, outfile)
            self.Gpn.get_Up_reps = self.get_Up_reps
        wp = kwargs.pop("wp", self.wp())
        self.BT = BruhatTitsTree(self.norm_p)
        verbose("Done initializing arithmetic groups")
        verbose("Done initialization of BigArithmeticGroup")

    def base_field(self):
        return self.F

    def quaternion_algebra(self):
        return self.Gn.B

    def clear_cache(self):
        self.Gn.clear_cache()
        if not self.use_shapiro():
            self.Gpn.clear_cache()

    def _repr_(self):
        return (
            "S-Arithmetic Rational Group attached to data p = %s,  disc = %s, level = %s"
            % (self.p, self.discriminant, self.level)
        )

    def prime(self):
        return self.p

    def use_shapiro(self):
        return self._use_shapiro

    def base_ring_local_embedding(self, prec=None):
        if self.F == QQ:
            if prec is not None:
                return self.F.hom([Qp(self.p, prec)(1)], check=False)
            else:
                return self.F.Hom(self.F).identity()
        else:
            self.local_splitting(prec)
            if hasattr(self.Gpn, "_F_to_local"):
                self.Gn._F_to_local = self._F_to_local
                return self._F_to_local
            else:
                self.Gpn._F_to_local = self._F_to_local
                return self._F_to_local

    @cached_method
    def get_gis_local(self, prec):
        return [self.embed(o, prec) for o in self.get_gis()]

    @cached_method
    def get_gitildes_local(self, prec):
        return [self.embed(o, prec) for o in self.get_gitildes()]

    @cached_method
    def get_gis(self):
        return [g**-1 for g in self.get_BT_reps()]

    @cached_method
    def get_gitildes(self):
        return [self.Gn.B(1)] + [g**-1 for g in self.get_BT_reps_twisted()[1:]]

    def clear_local_splitting(self):
        del self.Gpn._11
        del self.Gpn._II
        del self.Gpn._JJ
        del self.Gpn._KK

    def local_splitting(self, prec):
        r"""
        Finds an embedding of the definite quaternion algebra
        into the algebra of 2x2 matrices with coefficients in `\QQ_p`.

        INPUT:

        - prec -- Integer. The precision of the splitting.

        OUTPUT:

        - Matrices I, J, K giving the splitting.

        EXAMPLES::

            sage: from darmonpoints.sarithgroup import BigArithGroup
            sage: X = BigArithGroup(13,2*3,1,outfile='/tmp/darmonpoints.tmp') #  optional - magma
            sage: One, II, JJ, KK = X.local_splitting(10) #  optional - magma
            sage: B = X.Gn.B    #  optional - magma
            sage: II**2 == QQ(B.gen(0)**2) #  optional - magma
            True

        """
        if prec is None or prec <= self._prec:
            try:
                return self._11, self.Gpn._II, self.Gpn._JJ, self.Gpn._KK
            except AttributeError:
                pass
        (I, J, K), F_to_local = self.Gpn._compute_padic_splitting(self.ideal_p, prec)
        self._F_to_local = F_to_local
        self._11 = I.parent()(1)
        return self._11, I, J, K

    def save_to_db(self):
        fname = "arithgroup%s_%s_%s_%s.sobj" % (
            self.seed,
            self.p,
            self.discriminant,
            self.level,
        )
        self.db(fname)

    def small_group(self):
        return self.Gpn

    def large_group(self):
        return self.Gn

    def is_in_Gpn_order(self, x):
        return self.Gpn._is_in_order(x)

    def Gpn_Obasis(self):
        return self.Gpn._get_O_basis()

    def Gpn_denominator(self, x):
        return self.Gpn._denominator(x)

    def edge_from_quaternion(self, gamma):
        p = self.norm_p
        g = self.embed(gamma.conjugate(), 20)
        vv = min([o.valuation() for o in g.list()])
        g = p**-vv * g
        e = self.BT.opposite(self.BT.edge(g))
        e.set_immutable()
        return e

    def edges_leaving_even_vertex(self, gamma):
        return [g * gamma for g in self.get_BT_reps()]

    def edges_entering_odd_vertex(self, gamma):
        return [g * gamma for g in self.get_BT_reps_twisted()]

    @cached_method
    def get_BT_reps(self):
        reps = [self.Gpn.B(1)] + [None for i in range(self.p)]
        emb = self.get_embedding(20)
        matrices = [(i + 1, matrix(QQ, 2, 2, [i, 1, -1, 0])) for i in range(self.p)]
        if self._hardcode_matrices:  # DEBUG
            verbose("Using hard-coded matrices for BT")
            wp = self.wp()
            if self.F == QQ and self.discriminant == 1:
                lam = -wp.determinant()
            else:
                lam = -wp.reduced_norm()

            if self.F == QQ:
                alist = range(self.prime())
                pi = self.prime()
            else:
                alist = self.ideal_p.residues()
                pi = self.ideal_p.gens_reduced()[0]
            return [self.Gpn(1).quaternion_rep] + [
                1
                / self.prime()
                * wp
                * self.Gn.matrix_to_quaternion(
                    matrix(self.F, 2, 2, [1, -a, 0, self.prime()])
                )
                for a in alist
            ]
        else:
            wp = self.wp()
            try:
                lam = -wp.determinant()
            except AttributeError:
                lam = -wp.reduced_norm()
            n_iters = 0
            random = False if self.p <= 17 else True  # DEBUG - hardcoded bound here...
            for elt in self.Gn.enumerate_elements(random=random):
                n_iters += 1
                new_inv = elt**-1
                embelt = emb(elt)
                sk = lam * new_inv * wp**-1
                embsk = emb(sk)
                # if (embsk[0,0] - 1).valuation() > 0 and embsk[1,0].valuation() > 0\
                #    and all([not self.is_in_Gpn_order(o * new_inv) for o in reps if o is not None]):
                if (embelt[0, 0] - 1).valuation() > 0 and all(
                    [
                        not self.is_in_Gpn_order(o * new_inv)
                        for o in reps
                        if o is not None
                    ]
                ):
                    if hasattr(self.Gpn, "nebentypus"):
                        tmp = self.do_tilde(embelt) ** -1
                        tmp = tmp[0, 0] / (self.p ** tmp[0, 0].valuation())
                        tmp = ZZ(tmp.lift()) % self.Gpn.level
                        if tmp not in self.Gpn.nebentypus:
                            continue
                    if hasattr(self, "local_condition") and (
                        (self.local_condition(sk)[0, 0] - 1).valuation() == 0
                        or (self.local_condition(sk)[1, 0]).valuation() == 0
                    ):
                        continue
                    for idx, o1 in enumerate(matrices):
                        i, mat = o1
                        if is_in_Gamma0loc(embelt * mat, det_condition=False):
                            reps[i] = set_immutable(elt)
                            del matrices[idx]
                            verbose(
                                "%s, len = %s/%s"
                                % (n_iters, self.p + 1 - len(matrices), self.p + 1)
                            )
                            if len(matrices) == 0:
                                return reps
                            break

    def do_tilde(self, g, wp=None):
        if wp is None:
            wp = self.wp()
        if self.F == QQ and self.discriminant == 1:
            lam = -wp.determinant()
        else:
            lam = -wp.reduced_norm()
        ans = 1 / lam * wp * g * wp
        set_immutable(ans)
        return ans

    @cached_method
    def get_BT_reps_twisted(self):
        ans = [self.Gn.B(1)] + [self.do_tilde(g) for g in self.get_BT_reps()[1:]]
        _ = [set_immutable(o) for o in ans]
        return ans

    @cached_method
    def get_Up_reps(self):
        if self._hardcode_matrices:
            B = self.small_group().B
            try:
                pi = self.ideal_p.gens_reduced()[0]
                alist = list(self.ideal_p.residues())
            except AttributeError:
                pi = self.prime()
                alist = [a for a in range(pi)]

            Upreps0 = [
                Matrix(self.F, 2, 2, [pi, a, 0, 1]) for a in alist
            ]  # This was written for p-adic L-functions
            Upreps = [self.small_group().matrix_to_quaternion(o) for o in Upreps0]
            _ = [set_immutable(o) for o in Upreps]
            return Upreps
        else:
            wp = self.wp()
            lam = (
                -wp.determinant()
                if self.F == QQ and self.discriminant == 1
                else -wp.reduced_norm()
            )
            Upreps = [lam * o**-1 * wp**-1 for o in self.get_BT_reps()[1:]]
            _ = [set_immutable(o) for o in Upreps]
            return Upreps

    @cached_method
    def get_Up_reps_bianchi(self, pi, pi_bar):
        if not self._hardcode_matrices:
            raise NotImplementedError("For Bianchi, need to hardcode matrices")
        B = self.small_group().B
        # alist = range(self.prime())
        alist = list(self.ideal_p.residues())
        Upreps0 = [Matrix(self.F, 2, 2, [pi, a, 0, 1]) for a in alist]
        Upreps_bar0 = [Matrix(self.F, 2, 2, [pi_bar, a, 0, 1]) for a in alist]
        Upreps = [self.small_group().matrix_to_quaternion(o) for o in Upreps0]
        Upreps_bar = [self.small_group().matrix_to_quaternion(o) for o in Upreps_bar0]
        for o in Upreps:
            set_immutable(o)
        for o in Upreps_bar:
            set_immutable(o)
        return Upreps, Upreps_bar

    def get_covering(self, depth):
        return self.subdivide(
            [BTEdge(False, o) for o in self.get_BT_reps_twisted()], 1, depth - 1
        )

    def get_Zp_covering(self, depth):
        return self.subdivide(
            [BTEdge(False, o) for o in self.get_BT_reps_twisted()[1:]], 1, depth - 1
        )

    def get_edges_upto(self, depth):
        return [gamma for d in range(depth + 1) for rev, gamma in self.get_covering(d)]

    @cached_method
    def construct_edge_reps(self, depth):
        return {
            self.edge_from_quaternion(gamma): gamma
            for gamma in self.get_edges_upto(depth)
        }

    def subdivide(self, edgelist, parity, depth):
        if depth < 0:
            return []
        if depth == 0:
            for rev, gamma in edgelist:
                set_immutable(gamma)
                return edgelist
        newEgood = []
        for rev, gamma in edgelist:
            if parity % 2 == 0:
                newEgood.extend(
                    [BTEdge(not rev, e * gamma) for e in self.get_BT_reps_twisted()[1:]]
                )
            else:
                newEgood.extend(
                    [BTEdge(not rev, e * gamma) for e in self.get_BT_reps()[1:]]
                )
        return self.subdivide(newEgood, 1 - parity, depth - 1)

    def set_wp(self, wp):
        wp = self.quaternion_algebra()(wp)
        if self._hardcode_matrices:  # DEBUG, this is untested!
            self._wp = wp
            return self._wp
        epsinv = matrix(QQ, 2, 2, [0, -1, self.p, 0]) ** -1

        set_immutable(wp)
        ans = 0
        if not is_in_Gamma0loc(self.embed(wp, 20) * epsinv, det_condition=False):
            ans += 1
        if not all(
            self.Gpn._is_in_order(wp**-1 * g * wp) for g in self.Gpn._get_O_basis()
        ):
            ans += 2
        if not self.Gpn._is_in_order(wp):
            ans += 4
        # if hasattr(self, 'local_condition'):
        #     wp1 = self.local_condition(wp)
        #     if (wp1[0,0] - 1).valuation() == 0:
        #         ans += 8
        #     elif (wp1[1,1] - 1).valuation() == 0:
        #         ans += 8
        #     elif (wp1[1,0]).valuation() == 0:
        #         ans += 8

        #     if not all([o.valuation() > 0 for o in wp1.list()]):
        #         ans += 8
        if ans > 0:
            raise TypeError("Wrong wp (code %s)" % ans)
        self._wp = wp
        return self._wp

    @cached_method
    def embed_wp(self, prec):
        return self.embed(self.wp(), prec)

    def wp(self, **kwargs):
        if self._hardcode_matrices:
            return self.Gn.matrix_to_quaternion(
                matrix(self.F, 2, 2, [0, -1, self.prime(), 0])
            )
        try:
            return self._wp
        except AttributeError:
            pass
        verbose("Finding a suitable wp...")
        i = 0
        max_iterations = kwargs.get("max_iterations", -1)
        try:
            iter_candidates = self._iter_candidates
        except AttributeError:
            self._iter_candidates = self.Gn.generate_wp_candidates(
                self.p, self.ideal_p, **kwargs
            )
            iter_candidates = self._iter_candidates
        for wp in iter_candidates:
            if i % 50000 == 0:
                verbose("Done %s iterations" % i)
            if i == max_iterations:
                raise RuntimeError("Trouble finding wp by enumeration")
            i += 1
            try:
                wp = self.set_wp(wp)
            except TypeError:
                continue
            verbose("wp = %s" % list(wp))
            return wp

    def get_embedding(self, prec):
        r"""
        Returns an embedding of the quaternion algebra
        into the algebra of 2x2 matrices with coefficients in `\QQ_p`.

        INPUT:

        - prec -- Integer. The precision of the splitting.

        """
        if prec == -1:
            prec = self._prec
        if self.F == QQ and self.discriminant == 1:
            R = Qp(self.p, prec)

            def iota(q):
                return q.change_ring(R)

        else:
            mats = self.local_splitting(prec)
            v = self.base_ring_local_embedding(prec)

            def iota(q):
                try:
                    q = q.coefficient_tuple()
                except AttributeError:
                    q = q.list()
                return sum(v(a) * b for a, b in zip(q, mats))

        if prec > self._prec:  # DEBUG
            self._prec = prec
        return iota

    def embed(self, q, prec):
        try:
            q = q.quaternion_rep
        except AttributeError:
            pass
        if prec is None:
            return None
        elif prec == -1:
            prec = self._prec
        if self.F == QQ and self.discriminant == 1:
            return set_immutable(q.change_ring(Qp(self.p, prec)))
        else:
            v = self.base_ring_local_embedding(prec)
            if hasattr(q, "rows"):
                return set_immutable(q.apply_map(v))
            try:
                return set_immutable(self.Gn.quaternion_to_matrix(q).apply_map(v))
            except AttributeError:
                pass
            try:
                q = q.coefficient_tuple()
            except AttributeError:
                q = q.list()
            mats = self.local_splitting(prec)
            # return sum(v(o) * m for o, m in zip(q, self.local_splitting(prec))).change_ring(Qp(self.p, prec))
            return set_immutable(
                v(q[0]) + v(q[1]) * mats[1] + v(q[2]) * mats[2] + v(q[3]) * mats[3]
            )

    @cached_method
    def get_amalgam_reps(self):
        return [
            [o**-1 for o in self.get_BT_reps()],
            [o**-1 for o in self.get_BT_reps_twisted()],
        ]

    def reduce_in_amalgam(self, x, return_word=False, check=False):
        if return_word:
            a, wd = self._reduce_in_amalgam(set_immutable(x))
        else:
            try:
                a = self._reduce_fast(set_immutable(x))
            except RecursionError:
                raise RuntimeError("Error in reduce_in_amalgam: %s" % x)
        if check:
            assert self.is_in_Gpn_order(a)
            tmp = a
            reps = [self.get_BT_reps(), self.get_BT_reps_twisted()]
            for i, j in wd:
                tmp = tmp * reps[j][i]
            assert tmp == x
        if return_word:
            return a, wd
        else:
            return a

    def coset_reps(self):
        return self.get_BT_reps()

    @cached_method
    def get_coset_ti(self, x):
        a, wd = self.reduce_in_amalgam(x, return_word=True)
        assert len(wd) <= 1
        if len(wd) == 0:
            return a, 0
        else:
            assert len(wd) == 1
            assert wd[0][1] == 0
            return a, wd[0][0]

    def _reduce_fast(self, x, xl=None):
        p = self.p
        prec = 10
        if xl is None:
            xl = self.embed(x, prec)
        dval = lambda y, z: -min([o.valuation(p) for o in (y * z).list()])
        test_order = lambda y: is_in_Gamma0loc(y)

        if test_order(xl):
            return x
        else:
            gis = self.get_gis()
            gis_local = self.get_gis_local(prec)
            gitildes = self.get_gitildes()
            gitildes_local = self.get_gitildes_local(prec)
            wp = self.embed_wp(prec)
            xtilde = -(p**-1) * wp * xl * wp
            valx = dval(xtilde, 1)
            if valx == 0:
                valx = 1

            i = next(
                (i for i, gl in enumerate(gitildes_local) if dval(xtilde, gl) < valx),
                False,
            )
            if i:
                x = x * gis[i]
                xl = xl * gis_local[i]

            if test_order(xl):
                return set_immutable(x)

            valx = dval(xl, 1)
            if valx == 0:
                valx = 1
            i, g, gl = next(
                (
                    (i, g, gl)
                    for i, (g, gl) in enumerate(zip(gitildes, gitildes_local))
                    if dval(xl, gl) < valx
                ),
                (False, None),
            )
            if i:
                x = set_immutable(x * g)
                xl = xl * gl
            a = self._reduce_fast(x, xl)
            return set_immutable(a)

    def _reduce_in_amalgam(self, x):
        p = self.p
        # Local approach
        dval = lambda y: -min([o.valuation(p) for o in self.embed(y, 10).list()])
        test_order = lambda y: is_in_Gamma0loc(self.embed(y, 10))

        if test_order(x):
            return x, []
        else:
            gis = self.get_gis()
            gitildes = self.get_gitildes()
            xtilde = self.do_tilde(x)
            valx = dval(xtilde)
            if valx == 0:
                valx = 1

            i = next(
                (i for i, g in enumerate(gitildes) if dval(xtilde * g) < valx), False
            )
            x, new_wd = (x * gis[i], [(i, 0)]) if i else (x, [])

            if test_order(x):
                return set_immutable(x), new_wd

            valx = dval(x)
            if valx == 0:
                valx = 1
            i, g = next(
                ((i, g) for i, g in enumerate(gitildes) if dval(x * g) < valx),
                (False, None),
            )
            x, new_wd = (set_immutable(x * g), [(i, 1)] + new_wd) if i else (x, new_wd)

            if len(new_wd) == 0:
                print("Offending input: %s" % x)
                raise RuntimeError
            a, wd = self._reduce_in_amalgam(x)
            return set_immutable(a), wd + new_wd


def MatrixArithGroup(base=None, level=1, **kwargs):
    implementation = kwargs.get("implementation", None)
    if implementation not in ["coset_enum", "geometric"]:
        raise NotImplementedError
    if base is None:
        base = QQ
    if base == QQ:
        return ArithGroup_rationalmatrix(level, **kwargs)
    else:
        if base.signature() != (0, 1):
            raise NotImplementedError(
                "The base should be either QQ or an imaginary quadratic field."
            )
        if implementation == "coset_enum":
            return ArithGroup_nf_matrix_new(base, level, **kwargs)
        elif implementation == "geometric":
            return ArithGroup_nf_matrix(base, base(1), base(1), level, **kwargs)
        else:
            raise RuntimeError('Implementation should be "geometric" or "coset_enum"')


def ArithGroup(base, discriminant, abtuple=None, level=1, magma=None, **kwargs):
    nscartan = kwargs.get("nscartan", None)
    implementation = kwargs.get("implementation", None)
    if implementation is not None:
        if abtuple is not None:
            if abtuple != (1, 1):
                raise ValueError(
                    "Matrix implementations only available for matrix quaternion algebra"
                )
        else:
            if discriminant != 1:
                raise ValueError(
                    "Matrix implementations only available for matrix quaternion algebra"
                )
    if base == QQ:
        discriminant = ZZ(discriminant)
        if discriminant == 1:
            if nscartan is not None:
                from arithgroup_nscartan import ArithGroup_nscartan

                return ArithGroup_nscartan(nscartan, level, magma=magma, **kwargs)
            else:
                return ArithGroup_rationalmatrix(level, magma=magma, **kwargs)
        else:
            if magma is None:
                raise ValueError("Should specify magma session")
            if abtuple is not None:
                return ArithGroup_rationalquaternion(
                    abtuple, level, magma=magma, **kwargs
                )
            else:
                return ArithGroup_rationalquaternion(
                    discriminant, level, magma=magma, **kwargs
                )
    else:  # Number Field
        a, b = abtuple
        if magma is None:
            raise ValueError("Should specify magma session")
        if base.signature()[1] == 0:
            return ArithGroup_nf_fuchsian(base, a, b, level, magma=magma, **kwargs)
        else:
            if not is_page_initialized(magma):
                attach_kleinian_code(magma)
            if implementation is None:
                if (a, b) == (1, 1):
                    return MatrixArithGroup(
                        base, level, magma=magma, implementation="geometric", **kwargs
                    )
                else:
                    return ArithGroup_nf_kleinian(
                        base, a, b, level, magma=magma, **kwargs
                    )
            else:
                return MatrixArithGroup(base, level, magma=magma, **kwargs)
