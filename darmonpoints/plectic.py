## Implementing Plectic SH points
#################################
import os
from collections import defaultdict
from itertools import chain, groupby, islice, product, starmap, tee

from sage.algebras.quatalg.all import QuaternionAlgebra
from sage.functions.trig import arctan
from sage.groups.group import AlgebraicGroup
from sage.matrix.all import Matrix, matrix
from sage.misc.all import cached_method, lazy_attribute, walltime
from sage.misc.misc_c import prod
from sage.misc.persist import db
from sage.modular.arithgroup.congroup_gamma0 import Gamma0_constructor as Gamma0
from sage.modular.btquotients.btquotient import BruhatTitsTree
from sage.modular.cusps import Cusp
from sage.modules.all import vector
from sage.modules.free_module import FreeModule_generic
from sage.parallel.decorate import parallel
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

from .cohomology_arithmetic import ArithCoh, get_cocycle_from_elliptic_curve
from .homology import TrivialAction
from .homology_abstract import ArithHomology, HomologyGroup
from .sarithgroup import ArithGroup, BigArithGroup, BigArithGroup_class, BTEdge
from .sparse import *
from .util import *


def PlecticGroup(
    p1,
    p2,
    quat_data,
    level,
    base=None,
    grouptype=None,
    seed=None,
    magma=None,
    logfile=None,
    **kwargs,
):
    # global G, Coh, phiE, Phi, dK, J, J1, cycleGn, nn, Jlist
    config = configparser.ConfigParser()
    config.read("config.ini")
    param_dict = config_section_map(config, "General")
    param_dict.update(config_section_map(config, "Plectic"))
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

    a, b = quat_data
    if base is None:
        base = a.parent()
    discriminant = QuaternionAlgebra(base, a, b).discriminant()

    if grouptype is None:
        if base == QQ:
            grouptype = "PSL2"
        else:
            grouptype = "PSL2"  # DEBUG, was PGL2
    return PlecticGroup_class(
        base,
        p1,
        p2,
        discriminant,
        abtuple=(a, b),
        level=level,
        seed=seed,
        grouptype=grouptype,
        magma=magma,
        **kwargs,
    )


class PlecticGroup_class(AlgebraicGroup):
    r""" """

    def __init__(
        self,
        base,
        p0,
        p1,
        discriminant,
        abtuple,
        level=1,
        outfile=None,
        magma=None,
        **kwargs,
    ):
        self.F = base
        self.GS = ArithGroup(
            base,
            discriminant,
            abtuple,
            p0 * p1 * level,
            info_magma=kwargs.pop("info_magma", None),
            magma=magma,
            compute_presentation=False,
            **kwargs,
        )
        Gp0 = ArithGroup(
            base,
            discriminant,
            abtuple,
            p0 * level,
            info_magma=self.GS,
            magma=magma,
            compute_presentation=False,
            **kwargs,
        )
        Gp1 = ArithGroup(
            base,
            discriminant,
            abtuple,
            p1 * level,
            info_magma=self.GS,
            magma=magma,
            compute_presentation=False,
            **kwargs,
        )
        assert all(
            [
                Gp0._is_in_order(g) and Gp1._is_in_order(g)
                for g in self.GS._get_O_basis()
            ]
        )

        self.GS._init_kwargs = kwargs
        self.GS.embeddings = self.embeddings

        kwargs["Gpn"] = Gp0
        kwargs["Gn"] = Gp1
        G0 = BigArithGroup_class(
            base,
            p0,
            discriminant,
            abtuple=abtuple,
            level=level,
            extra_q=p1,
            outfile=outfile,
            info_magma=self.GS,
            magma=magma,
            **kwargs,
        )
        if not all(
            [
                G0.Gpn._is_in_order(g) and G0.Gn._is_in_order(g)
                for g in self.GS._get_O_basis()
            ]
        ):
            raise RuntimeError("Try again later...")

        kwargs["Gn"] = G0.Gpn
        kwargs["Gpn"] = G0.Gn
        G1 = BigArithGroup_class(
            base,
            p1,
            discriminant,
            abtuple=abtuple,
            level=level,
            extra_q=p0,
            outfile=outfile,
            info_magma=self.GS,
            magma=magma,
            **kwargs,
        )
        if not all(
            [
                G1.Gpn._is_in_order(g) and G1.Gn._is_in_order(g)
                for g in self.GS._get_O_basis()
            ]
        ):
            raise RuntimeError("Try again later...")

        self.GG = [G0, G1]
        self.ideal_p0 = G0.ideal_p
        self.ideal_p1 = G1.ideal_p
        self.discriminant = G0.discriminant
        self.level = level
        self._use_shapiro = False
        self.p = p0.norm()
        self.BT = BruhatTitsTree(self.p)
        estar = Matrix(ZZ, 2, 2, [0, 1, self.p, 0])  # edge v* -> vhat
        estar.set_immutable()
        self.estar = estar
        self.vstar = self.BT.origin(estar)
        self.vhat = self.BT.target(estar)
        self.depth = 1
        e0, e1 = self.embeddings()
        e00 = lambda o: e0(o, 5)
        e10 = lambda o: e1(o, 5)
        self.GG[0].local_condition = e10
        self.GG[1].local_condition = e00
        del self.GG[0]._wp
        del self.GG[1]._wp
        wp0 = self.GG[0].wp()
        wp1 = self.GG[1].wp()

    def small_group(self):
        return self.GS

    def base_field(self):
        return self.F

    def quaternion_algebra(self):
        return self.GG[0].Gpn.B

    def embeddings(self):
        return self.GG[0].embed, self.GG[1].embed

    def _repr_(self):
        return (
            "S-Arithmetic Rational Group attached to data \
       S = { (%s), (%s) }, \
       disc = %s, level = %s"
            % (
                self.ideal_p0.gens_reduced()[0],
                self.ideal_p1.gens_reduced()[0],
                self.discriminant,
                self.level,
            )
        )

    def prime(self):
        return self.p

    def use_shapiro(self):
        return False

    def edge_from_quaternion(self, g, g1, g2):
        return (op_edge_adj(self.BT, g1), op_edge_adj(self.BT, g2))

    # Centered at vhat
    @cached_method
    def construct_EV_dict(self, depth):
        p = self.p
        ans = defaultdict(list)
        for (e0, e1), h in self.construct_edge_reps(depth).items():
            v1 = self.GG[1].BT.origin(e1)
            ans[e0, v1].append(h)
            v1 = self.GG[1].BT.target(e1)
            ans[e0, v1].append(h)
        return {ky: val for ky, val in ans.items() if len(val) == p + 1}

    # Centered at vhat
    @cached_method
    def construct_VE_dict(self, depth):
        p = self.p
        ans = defaultdict(list)
        for (e0, e1), h in self.construct_edge_reps(depth).items():
            v0 = self.GG[0].BT.origin(e0)
            ans[v0, e1].append(h)
            v0 = self.GG[0].BT.target(e0)
            ans[v0, e1].append(h)
        return {ky: val for ky, val in ans.items() if len(val) == p + 1}

    # This is all centered at vhat
    @cached_method
    def construct_edge_reps(self, depth):
        prec = max(20, 2 * (depth + 1))
        print("Constructing edge reps for depth %s" % depth)
        edge_dict = {}
        total_iters = (self.p + 1) * (self.p**depth - 1) / (self.p - 1)
        n_iters = 0
        for g0 in self.GG[0].get_edges_upto(depth):
            n_iters += 1
            update_progress(
                float(n_iters) / total_iters,
                "Constructing edge reps for depth %s" % depth,
            )
            for g1 in self.GG[1].get_edges_upto(depth):
                h = g0 * g1
                h0 = self.GG[0].embed(h, prec)
                h1 = self.GG[1].embed(h, prec)
                edge_dict[self.edge_from_quaternion(h, h0, h1)] = (h, h0, h1)
        self.depth = depth
        return edge_dict

    def get_Up_reps_bianchi(self, pi, pi_bar):
        return self.GG[0].get_Up_reps(), self.GG[1].get_Up_reps()

    @cached_method
    def get_edge_rep(self, e0, e1):
        depth = self.depth
        while True:
            edge_dict = self.construct_edge_reps(depth)
            try:
                return edge_dict[e0, e1]
            except KeyError:
                depth += 1
                self.depth += 1

    def get_BT_reps(self, **kwargs):
        return [g * h for g, h in product(*[G.get_BT_reps() for G in self.GG])]

    def get_covering(self, depth):
        cov0 = self.GG[0].get_covering(depth)
        cov1 = self.GG[1].get_covering(depth)
        return product(cov0, cov1)

    # Centered at vhat
    def vert_depth(self, v0, v1):
        vhat = self.vhat
        a = len(self.GG[0].BT.find_geodesic(vhat, v0)) - 1
        b = len(self.GG[0].BT.find_geodesic(vhat, v1)) - 1
        return ZZ(max(a, b))
        assert (a - b) % 2 == 0
        return (ZZ(a + b).abs() + ZZ(a - b).abs()) / 2

    def reduce_in_amalgam(self, x, return_word=False, check=True):
        if return_word:
            c, wd2 = self.GG[1].reduce_in_amalgam(set_immutable(x), return_word=True)
            b, wd1 = self.GG[0].reduce_in_amalgam(set_immutable(c), return_word=True)
        else:
            c = self.GG[1].reduce_in_amalgam(set_immutable(x), return_word=False)
            b = self.GG[0].reduce_in_amalgam(set_immutable(c), return_word=False)
        if check:
            assert self.GG[0].Gpn._is_in_order(b)
            assert self.GG[1].Gpn._is_in_order(b)
        if return_word:
            return b, [wd1, wd2]
        else:
            return b

    def compute_presentation_GG(self):
        self.GG[0].Gpn._init_geometric_data(**self.GS._init_kwargs)
        self.GG[0].Gpn._compute_presentation = True
        self.GG[0].Gn._init_geometric_data(**self.GS._init_kwargs)
        self.GG[0].Gn._compute_presentation = True
        return

    def compute_presentation_GS(self):
        self.GS._init_geometric_data(**self.GS._init_kwargs)
        self.GS._compute_presentation = True
        return

    def get_degeneration(self, vv, f, idx):
        p = self.GG[idx].BT._p
        even = vv[idx].determinant().valuation(p) % 2 == 0
        elist = (
            self.GG[idx].BT.leaving_edges(vv[idx])
            if even
            else self.GG[idx].BT.entering_edges(vv[idx])
        )
        sgn = 1 if even else -1
        if idx == 0:
            return sgn * sum(f(e, vv[1]) for e in elist)
        else:
            return sgn * sum(f(vv[0], e) for e in elist)


# Computes nu0(phi)(gamma_{v0, e1})(v*,e*)
def get_nu0(G, phi, v0, e1, F=None, Co=0, Ce=0, scaling=1):
    BT = G.GG[1].BT
    p = BT._p
    VE_dict = G.construct_VE_dict(2)
    even = v0.determinant().valuation(p) % 2 == 0
    glist = VE_dict[G.vstar, G.estar] if even else VE_dict[G.vhat, G.estar]
    e0 = BT.leaving_edges(v0)[0] if even else BT.entering_edges(v0)[0]
    h = G.get_edge_rep(e0, e1)
    # h satisfies:
    # if even: h(e0, e1) = (e*, e*) for o(e0) = v0
    # if odd:  h(e0, e1) = (e*, e*) for t(e0) = v0
    # glist = G.GG[0].get_BT_reps() if even else G.GG[0].get_BT_reps_twisted()
    sgn = scaling if even else -scaling
    ans = (sgn * sum(evaluate_HC(G, phi, F, h, gi) for gi in glist))[0]
    return ans + Ce if even else ans + Co


def get_nu1(G, phi, e0, v1, F=None, Co=0, Ce=0, scaling=1):
    BT = G.GG[0].BT
    p = BT._p
    EV_dict = G.construct_EV_dict(2)

    even = v1.determinant().valuation(p) % 2 == 0
    glist = EV_dict[G.estar, G.vstar] if even else EV_dict[G.estar, G.vhat]

    e1 = BT.leaving_edges(v1)[0] if even else BT.entering_edges(v1)[0]
    assert BT.origin(e1) == v1 if even else BT.target(e1) == v1
    # glist = G.GG[1].get_BT_reps() if even else G.GG[1].get_BT_reps_twisted()
    sgn = scaling if even else -scaling
    ans = (
        sgn * sum(evaluate_HC(G, phi, F, G.get_edge_rep(e0, e1), gi) for gi in glist)
    )[0]
    return ans + Ce if even else ans + Co


def find_coboundaries(G, phi):
    BT = G.BT
    p = BT._p
    estar = G.estar
    vstar = G.vstar
    vhat = G.vhat

    f = lambda e0, v1: get_nu1(G, phi, e0, v1)
    h = lambda v0, e1: get_nu0(G, phi, v0, e1)
    fss = G.get_degeneration((vstar, vstar), f, 0)
    fsh = G.get_degeneration((vstar, vhat), f, 0)
    fhs = G.get_degeneration((vhat, vstar), f, 0)
    fhh = G.get_degeneration((vhat, vhat), f, 0)
    hss = G.get_degeneration((vstar, vstar), h, 1)
    hsh = G.get_degeneration((vstar, vhat), h, 1)
    hhs = G.get_degeneration((vhat, vstar), h, 1)
    hhh = G.get_degeneration((vhat, vhat), h, 1)
    #  + (p+1) * Cef  - (p+1) * Ceh = hss - fss
    #  + (p+1) * Cof  + (p+1) * Ceh = hsh - fsh
    #  - (p+1) * Cef  - (p+1) * Coh = hhs - fhs
    #  - (p+1) * Cof  + (p+1) * Coh = hhh - fhh

    # Cef Cof Ceh Coh
    A = Matrix(
        ZZ,
        4,
        4,
        [
            [p + 1, 0, -p - 1, 0],
            [0, p + 1, p + 1, 0],
            [-p - 1, 0, 0, -p - 1],
            [0, -p - 1, 0, p + 1],
        ],
    )
    b = Matrix(ZZ, 4, 1, [hss - fss, hsh - fsh, hhs - fhs, hhh - fhh])
    c = A.solve_right(b)

    scaling = lcm([o.denominator() for o in c.list()])
    print("scaling = %s" % scaling)
    phi = scaling * phi  # Fix scaling issue
    c *= scaling
    c = c.change_ring(ZZ)
    Cef, Cof, Ceh, Coh = c.list()
    print("c = %s" % str(c))
    f = lambda e0, v1: get_nu1(G, phi, e0, v1, Co=Cof, Ce=Cef)
    # h = lambda v0, e1 : get_nu0(G, phi, v0, e1, Co=Coh, Ce=Ceh) # DEBUG! much slower
    h = lambda v0, e1: Ceh if (v0.determinant().valuation(p) % 2 == 0) else Coh
    return phi, f, h


def evaluate_HC(G, phi, F, gamma, gamma_e, edge_dict=None, scaling=1):
    gamma_e_gamma = (
        gamma_e[0] * gamma[0],
        gamma_e[1] * gamma[1],
        gamma_e[2] * gamma[2],
    )
    if edge_dict is None:
        e_prime = None
        g = G.reduce_in_amalgam(gamma_e_gamma[0])
    else:
        e_prime = G.edge_from_quaternion(*gamma_e_gamma)
        g = gamma_e_gamma[0] * edge_dict[e_prime][0].conjugate()
    ans = scaling * phi.evaluate(g, check=False)
    if F is not None:
        V = ans.parent()
        e = G.edge_from_quaternion(*gamma_e)
        if e_prime is None:
            e_prime = G.edge_from_quaternion(*gamma_e_gamma)
        ans += V([F[e] - F[e_prime]])
    return ans


def op_edge_adj(self, M):
    p = self._p
    M = M.apply_map(lambda o: o.lift())
    a, b, c, d = M.list()
    M = Matrix(QQ, 2, 2, [-b * p, d, a * p, -c])

    v = min([M[i, j].valuation(p) for i in range(2) for j in range(2)])

    if v != 0:
        M = p ** (-v) * M

    det = M.determinant()
    if not det:
        raise NotImplementedError("matrix must be invertible")

    m00 = M[0, 0].valuation(p)
    m01 = M[0, 1].valuation(p)

    if m00 <= m01:
        tmp = det.valuation(p) - m00
        bigpower = p ** (1 + tmp)
        r = M[0, 0]
        if r != 0:
            r /= p**m00
        g, s, _ = r.xgcd(bigpower)
        r = (M[1, 0] * s) % bigpower
        newM = self._Mat_22([p**m00, 0, r, bigpower / p])
    else:
        tmp = det.valuation(p) - m01
        bigpower = p**tmp
        r = M[0, 1]
        if r != 0:
            r /= p**m01
        g, s, _ = r.xgcd(bigpower)
        r = (ZZ(M[1, 1]) * s) % bigpower
        newM = self._Mat_22([0, p**m01, bigpower, r])
    newM.set_immutable()
    return newM


def compute_edge_to_eqs(G, depth):
    edge_to_eqs = defaultdict(list)
    BT0 = G.GG[0].BT
    BT1 = G.GG[1].BT
    vhat = G.vhat
    p = BT0._p
    Fdict = {}
    vertex_list = get_vertex_list(BT0, vhat, depth)
    edge_list = get_edge_list(BT0, vhat, depth)

    n_vertices = len(vertex_list)
    i = 0
    total_iters = 2 * len(vertex_list) * len(edge_list)
    for v, e in product(vertex_list, edge_list):
        update_progress(float(i + 2) / total_iters, "Building edge_to_eqs dict")
        even = v.determinant().valuation(p) % 2 == 0
        if even:
            sgn = 1
            star_v0 = BT0.leaving_edges(v)
            star_v1 = BT1.leaving_edges(v)
        else:
            sgn = -1
            star_v0 = BT0.entering_edges(v)
            star_v1 = BT1.entering_edges(v)
        # Equation at (v,e) - involves h
        for e0 in star_v0:
            edge_to_eqs[e0, e].append(int(i))
        i += 1
        for e1 in star_v1:
            edge_to_eqs[e, e1].append(int(i))
        i += 1
    return edge_to_eqs


def compute_large_system_sparse_parallel(G, phi, ff, hh, depth):
    BT0 = G.GG[0].BT
    BT1 = G.GG[1].BT
    vhat = G.vhat
    p = BT0._p
    Fdict = {}
    vertex_list = get_vertex_list(BT0, vhat, depth)
    edge_list = get_edge_list(BT0, vhat, depth)
    edge_to_eqs = defaultdict(list)
    big_system = []
    n_vertices = len(vertex_list)
    i = 0
    total_iters = 2 * len(vertex_list) * len(edge_list)
    for v, e in product(vertex_list, edge_list):
        update_progress(float(i + 2) / total_iters, "Building up large system")
        even = v.determinant().valuation(p) % 2 == 0
        if even:
            sgn = 1
            star_v0 = BT0.leaving_edges(v)
            star_v1 = BT1.leaving_edges(v)
        else:
            sgn = -1
            star_v0 = BT0.entering_edges(v)
            star_v1 = BT1.entering_edges(v)
        # Equation at (v,e) - involves h
        big_system.append({(e0, e): 1 for e0 in star_v0})
        for e0 in star_v0:
            edge_to_eqs[e0, e].append(int(i))
        i += 1
        big_system.append({(e, e1): 1 for e1 in star_v1})
        for e1 in star_v1:
            edge_to_eqs[e, e1].append(int(i))
        i += 1
    return big_system, edge_to_eqs


def compute_indeps_parallel(G, phi, ff, hh, depth, njobs=1, max_cpus=1):
    BT0 = G.GG[0].BT
    BT1 = G.GG[1].BT
    vhat = G.vhat
    p = BT0._p
    Fdict = {}
    vertex_list = get_vertex_list(BT0, vhat, depth)
    edge_list = get_edge_list(BT0, vhat, depth)
    indeps = []

    n_vertices = len(vertex_list)
    i = 0
    total_iters = 2 * len(vertex_list) * len(edge_list)
    arg_list = [(ff, hh, []) for _ in range(njobs)]
    for v, e in product(vertex_list, edge_list):
        update_progress(float(i + 2) / total_iters, "Building up indeps")
        even = v.determinant().valuation(p) % 2 == 0
        if even:
            sgn = 1
        else:
            sgn = -1
        arg_list[(i // 2) % njobs][2].append((sgn, v, e, i))
        i += 2
    print("Now computing independent term...")

    nrows = i
    indeps = [0 for _ in range(nrows)]

    @parallel(ncpus=max_cpus)
    def get_coeffs_aux(ff, hh, W, progress_bar=False):
        ans = []
        niters = len(W)
        for j, (sgn, v, e, i) in enumerate(W):
            if progress_bar:
                update_progress(float(j) / niters, "")
            ans.append((i, int(sgn * ff(e, v)), int(sgn * hh(v, e))))
        return ans

    if njobs == 1:
        for i, fval, hval in get_coeffs_aux(*arg_list[0], progress_bar=True):
            indeps[i] = int(hval)
            indeps[i + 1] = int(fval)
    else:
        j = 0
        for _, lst in get_coeffs_aux(arg_list):
            for i, fval, hval in lst:
                update_progress(float(j) / nrows, "j = %s (%s)" % (j, nrows))
                j += 2
                indeps[i] = int(hval)
                indeps[i + 1] = int(fval)
    return indeps


def sample_point(h, r0, r1, prec=20):
    ans = []
    _, h0, h1 = h
    a, b, c, d = h0.list()
    pt = -d / c if r0 else -b / a
    ans.append(pt.parent()(pt))
    a1, b1, c1, d1 = h1.list()
    pt = -d1 / c1 if r1 else -b1 / a1
    ans.append(pt.parent()(pt))
    return ans


def do_twist(G, gamma, tau0, tau1):
    Kp = tau0.parent()
    wp = G.GG[0].wp() * G.GG[1].wp()
    a, b, c, d = (Kp(o) for o in G.GG[0].embed(wp, 10).list())
    tau0 = (a * tau0 + b) / (c * tau0 + d)
    Kp = tau1.parent()
    a, b, c, d = (Kp(o) for o in G.GG[1].embed(wp, 10).list())
    tau1 = (a * tau1 + b) / (c * tau1 + d)
    gamma = wp * gamma * wp**-1
    return gamma, tau0, tau1


def riemann_sum(
    G,
    tau0,
    tau1,
    gamma,
    Phi,
    depth=1,
    progress_bar=True,
    max_iters=-1,
    F=None,
    twist=True,
    edge_dict=None,
):
    if F is None:
        F = {}
    prec = max([20, 2 * depth])
    ans = 0
    if twist:
        tau0, tau1, gamma = do_twist(G, tau0, tau1, gamma)

    tau0bar, tau1bar = tau0.trace() - tau0, tau1.trace() - tau1
    p = tau0.parent().prime()
    K = Qp(p, prec)
    res = Matrix(K, 2, 2, 0)
    n_ints = 0
    projection = lambda z: z._polynomial_list(pad=True)
    ncover = ((p + 1) * p ** (depth - 1)) ** 2
    cov0 = [
        (r0, he0, G.GG[0].embed(he0, prec), G.GG[1].embed(he0, prec))
        for r0, he0 in G.GG[0].get_covering(depth)
    ]
    cov1 = [
        (r1, he1, G.GG[0].embed(he1, prec), G.GG[1].embed(he1, prec))
        for r1, he1 in G.GG[1].get_covering(depth)
    ]
    gamma = (gamma, G.GG[0].embed(gamma, prec), G.GG[1].embed(gamma, prec))
    for (r0, he0, he00, he01), (r1, he1, he10, he11) in product(cov0, cov1):
        he = (he0 * he1, he00 * he10, he01 * he11)
        assert G.GG[0].embed(he[0], prec) == he[1]
        assert G.GG[1].embed(he[0], prec) == he[2]
        if progress_bar:
            update_progress(float(RealField(10)(n_ints) / ncover), "Riemann sum")
        n_ints += 1
        val = ZZ(evaluate_HC(G, Phi, F, gamma, he, edge_dict=edge_dict)[0])
        if val == 0:
            continue
        tee = sample_point(he, r0, r1, prec)
        if tee[0] == Infinity or tee[1] == Infinity:
            continue
        hte0 = projection(
            ((tau0.parent()(tee[0]) - tau0) / (tau0.parent()(tee[0]) - tau0bar)).log()
        )
        hte1 = projection(
            ((tau1.parent()(tee[1]) - tau1) / (tau1.parent()(tee[1]) - tau1bar)).log()
        )
        res[0, 0] += val * hte0[0] * hte1[0]
        res[0, 1] += val * hte0[0] * hte1[1]
        res[1, 0] += val * hte0[1] * hte1[0]
        res[1, 1] += val * hte0[1] * hte1[1]
        if n_ints == max_iters:
            return res
    return [o.add_bigoh(depth) for o in res.list()]


def riemann_sum_parallel(
    G, tau0, tau1, gammaquatrep, phiE, depth, Fdict, njobs=1, twist=True, max_cpus=1
):
    arg_list = [
        (G, tau0, tau1, gammaquatrep, phiE, depth, Fdict, i, njobs, twist)
        for i in range(njobs)
    ]

    @parallel(ncpus=max_cpus)
    def riemann_sum_parallel_aux(
        G, tau0, tau1, gamma, Phi, depth, F, idx, njobs, twist=True, progress_bar=False
    ):
        from itertools import islice

        edge_dict = G.construct_edge_reps(depth)
        if F is None:
            F = {}
        prec = max([20, 2 * depth])
        ans = 0
        if twist:
            gamma, tau0, tau1 = do_twist(G, gamma, tau0, tau1)
        tau0bar, tau1bar = tau0.trace() - tau0, tau1.trace() - tau1
        p = tau0.parent().prime()
        K = Qp(p, prec)
        res = 0
        projection = lambda z: z._polynomial_list(pad=True)[0]
        cov0 = [
            (r0, he0, G.GG[0].embed(he0, prec), G.GG[1].embed(he0, prec))
            for r0, he0 in G.GG[0].get_covering(depth)
        ]
        cov1 = [
            (r1, he1, G.GG[0].embed(he1, prec), G.GG[1].embed(he1, prec))
            for r1, he1 in G.GG[1].get_covering(depth)
        ]
        gamma = (gamma, G.GG[0].embed(gamma, prec), G.GG[1].embed(gamma, prec))
        n_iters = 0
        total_iters = len(cov0) * len(cov1) // njobs
        for (r0, he0, he00, he01), (r1, he1, he10, he11) in islice(
            product(cov0, cov1), idx, None, njobs
        ):
            n_iters += 1
            if progress_bar:
                update_progress(float(n_iters) / (total_iters), "Riemann sum")
            he = (he0 * he1, he00 * he10, he01 * he11)
            gamma_e_gamma = (he[0] * gamma[0], he[1] * gamma[1], he[2] * gamma[2])
            e = G.edge_from_quaternion(*he)
            e_prime = G.edge_from_quaternion(*gamma_e_gamma)
            g = gamma_e_gamma[0] * edge_dict[e_prime][0].conjugate()
            val = Phi.evaluate(g, check=False)[0]
            val += F[e] - F[e_prime]
            if val == 0:
                continue
            tee = sample_point(he, r0, r1, prec)
            if tee[0] == Infinity or tee[1] == Infinity:
                continue
            hte0 = projection(
                (
                    (tau0.parent()(tee[0]) - tau0) / (tau0.parent()(tee[0]) - tau0bar)
                ).log()
            )
            hte1 = projection(
                (
                    (tau1.parent()(tee[1]) - tau1) / (tau1.parent()(tee[1]) - tau1bar)
                ).log()
            )
            res += val * hte0 * hte1
        return res.add_bigoh(depth)

    if njobs == 1:
        return riemann_sum_parallel_aux(*arg_list[0], progress_bar=True)
    else:
        ans = 0
        for nfin, (_, val) in enumerate(riemann_sum_parallel_aux(arg_list)):
            update_progress(
                float(nfin) / njobs, "finished jobs / total = %s/%s" % (nfin + 1, njobs)
            )
            try:
                ans += val
            except TypeError:
                print("An error occurred, printing output")
                print(val)
                raise RuntimeError
        return ans


def get_cycle(G, beta, prec):
    p = G.p
    F_to_Qp = G.GG[0].base_ring_local_embedding(prec)
    gamma_zeta, zeta = G.GG[0].Gn.embed_order(p, beta, prec, F_to_Qp=F_to_Qp)
    gammaquatrep = gamma_zeta.quaternion_rep
    iota0 = G.GG[0].get_embedding(prec)
    iota1 = G.GG[1].get_embedding(prec)
    Cp = Qq(p**2, prec, names="g")
    g = Cp.gen()
    a, b, c, d = iota0(gammaquatrep).list()
    D0 = our_sqrt(Cp((a + d) ** 2 - 4))
    tau0 = (Cp(a - d) + D0) / Cp(2 * c)
    a, b, c, d = iota1(gammaquatrep).list()
    D1 = our_sqrt(Cp((a + d) ** 2 - 4))
    tau1 = (Cp(a - d) + D1) / Cp(2 * c)
    return gammaquatrep, tau0, tau1


def get_edge_list(BT, center, depth):
    ans = []
    opp = True
    for i in range(depth):
        new_ans = BT.get_balls(center, level=i)
        if opp:
            ans.extend([BT.opposite(e) for e in new_ans])
        else:
            ans.extend(new_ans)
        opp = not opp
    for o in ans:
        o.set_immutable()
    return ans


def get_vertex_list(BT, center, depth):
    ans = []
    for i in range(depth):
        new_ans = list(set([BT.origin(o) for o in BT.get_balls(center, level=i)]))
        ans.extend(new_ans)
    for o in ans:
        o.set_immutable()
    return ans


def lift_to_HC(G, phiE, depth, njobs=1, max_cpus=1):
    phiE, f, h = find_coboundaries(G, phiE)
    b = compute_indeps_parallel(G, phiE, f, h, depth, njobs=njobs, max_cpus=max_cpus)
    A, edge_to_eqs = compute_large_system_sparse_parallel(G, phiE, f, h, depth)
    Fdict = compute_lift_sparse_cy(A, b, edge_to_eqs)
    return phiE, Fdict


def compute_plectic_point(
    G, phiE, Fdict, depth, beta, njobs=1, max_cpus=1, outfile=None
):
    gammaquatrep, tau0, tau1 = get_cycle(
        G, beta, 20
    )  # 20 is the precision, okay for now
    fwrite("gammaquatrep = %s" % gammaquatrep, outfile)
    fwrite("tau0 = %s" % tau0, outfile)
    fwrite("tau1 = %s" % tau1, outfile)
    return riemann_sum_parallel(
        G, tau0, tau1, gammaquatrep, phiE, depth, Fdict, njobs=njobs, max_cpus=max_cpus
    )


def additive_integral(mu, phi):
    r"""
    Calculates the additive integral of the rational function phi against mu.
    """
    phi_rat = [o.rational_function() for o in phi]
    R = PowerSeriesRing(phi_rat[0].parent().base_ring(), "z")
    base = phi_rat[0].parent().base_ring().base_ring()
    R0 = PowerSeriesRing(base, "z")
    projection = lambda f: (
        f.map_coefficients(
            lambda o: o._polynomial_list(pad=True)[0], new_base_ring=base
        ),
        f.map_coefficients(
            lambda o: o._polynomial_list(pad=True)[1], new_base_ring=base
        ),
    )

    c = [phi(0) for phi in phi_rat]
    pol0, pol1 = (
        projection(R(c0.log()) + R(phi / c0).log()) for c0, phi in zip(c, phi_rat)
    )
    ans = Matrix(base, 2, 2, 0)
    S = mu.parent().analytic_functions()
    S0 = S.base_ring()
    for u, v in product([0, 1], repeat=2):
        ff = S0(pol0[u]) * S(pol1[v])
        ans[u, v] = mu.evaluate_at_poly(ff)
    return ans


def check_is_cycle(G, cycle_list):
    emb0 = G.GG[0].embed
    emb1 = G.GG[1].embed
    ans0 = 0
    ans1 = 0
    for sgn, gamma, D0, D1 in cycle_list:
        ans0 += sgn * (
            emb0(gamma**-1, 20).change_ring(D0.parent().base_ring()) * D0 - D0
        )
        ans1 += sgn * (
            emb1(gamma**-1, 20).change_ring(D1.parent().base_ring()) * D1 - D1
        )
    print(ans0 == 0)
    print(ans1 == 0)
