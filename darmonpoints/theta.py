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
        return (a * z + b) / (c * z + d) #a / c + (b - a * d / c) / (c * z + d)
    except PrecisionError:
        return Infinity
    except TypeError:
        emb = z.parent().embedding_from_subfield
        a, b, c, d = emb(a), emb(b), emb(c), emb(d)
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
    def __init__(self, G, a=0, b=None, prec=None, **kwargs):
        K = kwargs.get("base_ring", None)
        if K is None:
            K = G.K
        self.K = K
        self.G = G
        self.p = G.pi
        generators = G.generators()
        balls = G.balls
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
            D = self.Div([(1, a), (-1, b)])
        self.a = a
        self.b = b
        self.D = D
        self.m = 1
        self.z = K['z'].gen()

        params = G.parameters
        gens_ext = G.gens_extended()

        # self.val will contain the 0 and 1 terms
        D1 = sum((g * D for (i, g), tau in zip(gens_ext, params)), self.Div([]))
        self.val = self.z.parent()(1)
        self.val *= prod((self.z - P) ** n for P, n in (D + D1))
        self.Fnlist = [{}]
        D1dict = {i : g * D for (i, g), tau in zip(gens_ext,params)}
        for (i, g), tau in zip(gens_ext,params):
            gD = sum(
                g * val for j, val in D1dict.items() if j != -i
            )
            self.Fnlist[0][i] = MeromorphicFunctions(self.K, self.p, self.prec)(gD, tau)

    def improve(self, m):
        gens_ext = self.G.gens_extended()
        params = self.G.parameters
        for it in range(m):
            if self.m >= self.prec:
                return self
            tmp = {}
            for (i, gi), tau in zip(gens_ext, params):
                for j, Fj in self.Fnlist[-1].items():
                    if i != -j:
                        vl = Fj.left_act_by_matrix(gi, tau)
                        try:
                            tmp[i] += vl
                        except KeyError:
                            tmp[i] = vl
            self.Fnlist.append(tmp)
            self.m += 1
        return self

    def improve_one(self):
        return self.improve(1)

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
        if isinstance(z, DivisorsElement):
            return prod(self(P, **kwargs) ** n for P, n in z)
        G = self.G
        recursive = kwargs.get("recursive", False)
        ans = 1
        if recursive:
            z0, wd = G.to_fundamental_domain(z)
            wdab = word_to_abelian(wd, len(G.generators()))
            ans *= prod(
                G.u_function(g, self.prec).evaluate(self.D, recursive=False) ** i
                for g, i in zip(G.generators(), wdab)
                if i != 0
            )
        else:
            z0 = z
        ans *= self.val(z0)
        ans *= prod(F(z0) for FF in self.Fnlist for ky, F in FF.items())
        return ans

    def eval_derivative(self, z, recursive=False):
        if recursive and not G.in_fundamental_domain(z, strict=False):
            raise NotImplementedError("Recursivity not implemented for derivative")
        if isinstance(z, DivisorsElement):
            return prod(self.eval_derivative(P, recursive=recursive) ** n for P, n in z)

        v0 = self.val(z)
        Fnz = {}
        for FF in self.Fnlist:
            for ky, F in FF.items():
                Fz = F(z)
                try:
                    Fnz[ky] *= Fz
                except KeyError:
                    Fnz[ky] = Fz
        # val' * Fn(z)
        Fnzall = prod((o for o in Fnz.values()))
        valder = self.val.derivative()(z)

        v0 = self.val(z) * Fnzall
        # need to add the terms of val * Fn'
        tmp = sum(f.eval_derivative(z) / f(z) for FF in self.Fnlist for f in FF.values())
        return valder * Fnzall + tmp * v0
