from copy import copy, deepcopy
from itertools import chain

from sage.categories.groups import Groups
from sage.functions.generalized import sgn
from sage.groups.matrix_gps.linear import GL
from sage.matrix.matrix_space import MatrixSpace
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex
from sage.misc.verbose import verbose
from sage.modules.module import Module
from sage.rings.all import ZZ, IntegerRing
from sage.rings.infinity import Infinity
from sage.rings.semirings.non_negative_integer_semiring import NN
from sage.sets.set import Set
from sage.structure.element import Element, ModuleElement
from sage.structure.parent import Parent
from sage.structure.richcmp import richcmp
from sage.structure.sage_object import SageObject
from sage.structure.unique_representation import UniqueRepresentation

from .divisors import Divisors, DivisorsElement
from .meromorphic import *

infinity = Infinity


def eval_rat(D, z):
    if z == Infinity:
        return D.parent().base_ring()(1)
    if not hasattr(z, "parent"):
        z = ZZ(z)
    ans = z.parent()(1) * D.parent().base_ring()(1)
    fails = 0
    for P, n in D:
        if P == Infinity:
            continue
        zP = z - P
        if zP == 0:
            fails += n
        else:
            ans *= zP**n
    # assert fails == 0 # DEBUG !
    return ans


def eval_rat_derivative(D, z):
    ans = 0
    fails = 0
    for P, n in D:
        if P == Infinity:
            continue
        zP = z - P
        if zP == 0:
            fails += n
        else:
            ans += n * zP**-1
    # assert fails == 0 # DEBUG !
    return ans * eval_rat(D, z)


def act(mtrx, z):
    """
    Compute the action of a 2x2 matrix on an element.

    If the base field is Qp, we first "normalize" mtrx to avoid
    precision loss.
    """
    a, b, c, d = mtrx.list()
    if z is Infinity:
        return Infinity if c == 0 else a / c
    try:
        return (a * z + b) / (c * z + d)
    except PrecisionError:
        return Infinity


def element_to_matrix(wd, generators):
    ans = wd(generators)
    ans.set_immutable()
    return ans


def word_to_abelian(wd, g):
    try:
        wd = wd.Tietze()
    except AttributeError:
        pass
    wdab = [0 for i in range(g)]
    for i in wd:
        wdab[abs(i) - 1] += sgn(i)
    return (ZZ**g)(wdab)


class ThetaOC(SageObject):
    def __init__(self, G, a=None, b=None, prec=None, **kwargs):
        K = kwargs.get("base_ring", None)
        if K is None:
            K = G.K
        self.K = K
        self.G = G
        self.p = G.pi
        _ = G.generators()
        _ = G.balls()
        if prec is None:
            try:
                self.prec = K.precision_cap()
            except AttributeError:
                self.prec = None
        else:
            self.prec = prec
        self.Div = Divisors(K)
        if b is None:
            D = self.Div(a)
            if D.degree() != 0:
                raise ValueError(
                    "Must specify a degree-0 divisor, or parameters a and b"
                )
        else:
            D = self.Div([(1, K(a)), (-1, K(b))])
        D = G.find_equivalent_divisor(D)
        self.a = a
        self.b = b
        self.m = 1
        self.z = K["z"].gen()
        self.MM = MeromorphicFunctions(self.K, self.p, self.prec)
        params = G.parameters
        gens_ext = G.gens_extended()
        
        # Corresponding to words of length exactly 1
        D1dict = {i : g * D for i, g in gens_ext}

        # Corresponding to words of length exactly 2
        # D2dict = {i : sum(g * val) for j, val in D1dict.items() if j != i for i, g in gens_ext }
        
        # self.val will contain the 0, 1 and 2 terms
        self.val = sum(D1dict.values(), D)
        self.Fnlist = [{ i :
            self.MM(sum(g * val for j, val in D1dict.items() if j != -i), tau)
                for (i, g), tau in zip(gens_ext, params)}]

    def improve(self, m):
        gens_ext = self.G.gens_extended()
        params = self.G.parameters
        action_data = {}
        for (i, gi), tau in zip(gens_ext, params):
            for j, Fj in self.Fnlist[-1].items():
                if i != -j:
                    action_data[i, j] = (
                        self.MM.get_action_data(gi, Fj._parameter, tau),
                        tau,
                    )
        for it in range(m):
            if self.m >= self.prec:
                if len(self.Fnlist) > 0:
                    self.Fnlist = [
                    {
                        ky: sum((F[ky] for F in self.Fnlist[1:]), self.Fnlist[0][ky])
                        for ky in self.Fnlist[0]
                    }
                    ]
                return self
            tmp = {}
            for (i, gi), tau in zip(gens_ext, params):
                for j, Fj in self.Fnlist[-1].items():
                    if i != -j:
                        vl = Fj.fast_act(action_data[i, j])
                        try:
                            tmp[i] += vl
                        except KeyError:
                            tmp[i] = vl
            self.Fnlist.append(tmp)
            self.m += 1
        self.Fnlist = [
            {
                ky: sum((F[ky] for F in self.Fnlist[1:]), self.Fnlist[0][ky])
                for ky in self.Fnlist[0]
            }
        ]
        return self

    def _repr_(self):
        a, b = self.a, self.b
        if b is None:
            try:
                lst = a.as_list_of_differences()
                if len(lst) == 1:
                    a, b = lst[0]
            except AttributeError:
                pass
        try:
            a = a.lift()
            b = b.lift()
        except AttributeError:
            pass
        return f"Θ(z;{a},{b})_{{{self.m}}}"

    def _latex_(self):
        a, b = self.a, self.b
        if b is None:
            try:
                lst = a.as_list_of_differences()
                if len(lst) == 1:
                    a, b = lst[0]
            except AttributeError:
                pass
        try:
            a = a.lift()
            b = b.lift()
        except AttributeError:
            pass
        try:
            a = a.rational_reconstruction()
            b = b.rational_reconstruction()
        except AttributeError:
            pass
        return f"\\Theta(z;{latex(a)},{latex(b)})_{{{latex(self.m)}}}"

    def __call__(self, z, **kwargs):
        return self.evaluate(z, **kwargs)

    def evaluate(self, z, **kwargs):
        if not isinstance(z, DivisorsElement):
            z = self.Div([(1, z)])
        if z.degree() != 0:
            z -= self.Div([(z.degree(), Infinity)])
        z = self.G.find_equivalent_divisor(z)
        ans0 = prod(eval_rat(self.val, P) ** n for P, n in z)
        ans1 = prod(F(z) for FF in self.Fnlist for F in FF.values())        
        return ans0 * ans1

    def eval_derivative(self, z, return_value=False):
        if isinstance(z, DivisorsElement):
            raise NotImplementedError
        z0, wd = self.G.to_fundamental_domain(z)
        gens = (
            [None]
            + self.G.generators()
            + [o.adjugate() for o in reversed(self.G.generators())]
        )
        g = prod((gens[i] for i in wd), gens[1].parent()(1)).adjugate()
        assert act(g, z) == z0
        a, b, c, d = g.list()
        ans = (a * d - b * c) * (c * z + d) ** -2
        z = z0
        vz = eval_rat(self.val, z)
        Fnz = {}
        for FF in self.Fnlist:
            for ky, F in FF.items():
                FP = F(z)
                try:
                    Fnz[ky] *= FP
                except KeyError:
                    Fnz[ky] = FP
        Fnzall = prod((o for o in Fnz.values()))
        valder = eval_rat_derivative(self.val, z)

        v0 = vz * Fnzall
        # need to add the terms of val * Fn'
        tmp = sum(
            f.eval_derivative(z) / f(z) for FF in self.Fnlist for f in FF.values()
        )
        ans *= valder * Fnzall + tmp * v0
        if return_value:
            return ans, v0
        else:
            return ans
