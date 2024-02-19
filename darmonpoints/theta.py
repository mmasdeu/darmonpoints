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

def act(mtrx,z):
    """
    Compute the action of a 2x2 matrix on an element.

    If the base field is Qp, we first "normalize" mtrx to avoid 
    precision loss.
    """
    if mtrx == 1:
        return z
    br = mtrx.base_ring()
    if br.is_subring(QQ):
        a, b, c, d = mtrx.list()
    else:
        pp = br.prime()
        min_val = min([o.valuation() for o in mtrx.list()])
        new_mtrx = pp**(-min_val) * mtrx
        a, b, c, d = new_mtrx.list()

    if z is Infinity:
        return Infinity if c == 0 else a / c
    try:
        ans = (a*z+b)/d if c == 0 else a/c + (b-a*d/c)/(c*z+d)
    except PrecisionError:
        return Infinity
    except TypeError:
        emb = z.parent().embedding_from_subfield
        a,b,c,d = emb(a), emb(b), emb(c), emb(d)
        try:
            ans = (a*z+b)/d if c == 0 else a/c + (b-a*d/c)/(c*z+d)
        except PrecisionError:
            return Infinity
    return ans

@cached_function
def find_eigenvector_matrix(g):
    vaps = sorted([o for o, _ in g.charpoly().roots()], key=lambda o: o.valuation())
    verb_level = get_verbose()
    set_verbose(0)
    veps = sum(((g - l).right_kernel().basis() for l in vaps), [])
    set_verbose(verb_level)
    return g.matrix_space()(veps).transpose()

@cached_function
def find_parameter(g, r, pi=None, ball=None, check=True):
    if pi is None:
        pi = g.parent().base_ring().uniformizer()
    if ball is not None:
        assert r == ball.radius
    ans = copy(find_eigenvector_matrix(g).adjugate())
    # column 0 means that the boundary of B_g (the ball attached to g)
    # gets sent to the circle of radius 1.
    # Concretely, if B_g = B(a, p^-r), we send a+p^r |-> 1.
    # As a consequence, P^1-B_g gets sent to the closed ball B(0,1).
    z0 = ball.center.lift_to_precision() + pi ** ZZ(ball.radius)
    if check:
        assert z0 in ball.closure() and z0 not in ball
    lam = (ans[0, 0] * z0 + ans[0, 1]) / (ans[1, 0] * z0 + ans[1, 1])
    ans.rescale_row(0, 1 / lam)
    ans.set_immutable()
    if check:
        if act(ans, z0) != 1:
            raise RuntimeError
        if ans * ball.complement() != ball.parent()(0, 0).closure():
            # print(ans * ball.complement())
            # print(ball.parent()(0,0).closure())
            raise RuntimeError
    return ans

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
        K = kwargs.get('base_ring',None)
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
        gens = [(i + 1, o) for i, o in enumerate(generators)]
        gens.extend([(-i, o**-1) for i, o in gens])
        self.gens = tuple(
            (i, o, find_parameter(o, balls[i].radius, self.p, ball=balls[i]))
            for i, o in gens
        )
        for i, o, t in self.gens:
            o.set_immutable()
            t.set_immutable()
        if b is None:
            D = self.Div(a)
            if D.degree() != 0:
                raise ValueError(
                    "Must specify a degree-0 divisor, or parameters a and b"
                )
        else:
            D = self.Div([(1,a), (-1,b)])
        # if not all(G.in_fundamental_domain(P, strict=False) for P, n in D):
        #     raise ValueError("Divisor should be supported on fundamental domain.")
        self.a = a
        self.b = b
        self.D = D
        self.m = 1
        PP = PolynomialRing(K, names="z")
        self.z = PP.gen()

        # self.val will contain the 0 and 1 terms
        D1 = sum((g * D for i, g, tau in self.gens), self.Div([]))
        self.val = prod(((self.z - P) ** n for P, n in (D + D1)), PP(1))
        self.Fn0 = {}
        D1dict = {}
        for i, g, tau in self.gens:
            D1dict[i] = g * D
        for i, g, tau in self.gens:
            gD = sum(
                g * val for ky, val in D1dict.items() if ky != -i
            )  # DEBUG - only works when wd is a 1-tuple!
            self.Fn0[i] = MeromorphicFunctions(self.K, self.p, self.prec)(gD, tau)
        self.Fn = self.Fn0

    def improve(self, m):
        for it in range(m):
            if self.m >= self.prec:
                return self
            newFn = deepcopy(self.Fn0)
            for i, gi, tau in self.gens:
                for j, Fj in self.Fn.items():
                    if i != -j:
                        newFn[i] += Fj.left_act_by_matrix(gi, tau)
            self.Fn = newFn
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
        recursive = kwargs.get('recursive', False)
        ans = 1
        if recursive:
            z0, wd = G.to_fundamental_domain(z)
            wdab = word_to_abelian(wd, len(G.generators()))
            ans *= prod(
                G.u_function(g, self.prec).evaluate(self.D, recursive=False) ** i
                for g, i in zip(G.generators(), wdab) if i != 0
            )
        else:
            z0 = z
        ans *= self.val(z0)
        ans *= prod(F(z0) for ky, F in self.Fn.items())
        return ans

    def eval_derivative(self, z, recursive=False):
        if recursive and not G.in_fundamental_domain(z, strict=False):
            raise NotImplementedError("Recursivity not implemented for derivative")
        if isinstance(z, DivisorsElement):
            return prod(self.eval_derivative(P, recursive=recursive) ** n for P, n in z)
        v0 = self.val(z)
        Fnz = {}
        for ky, F in self.Fn.items():
            Fnz[ky] = F(z)
        ans = prod((o for o in Fnz.values()), self.val.derivative()(z))
        for ky0 in self.Fn:
            ans += v0 * prod(
                (Fnz[ky] for ky, F in Fnz.items() if ky != ky0),
                self.Fn[ky0].eval_derivative(z),
            )
        return ans
