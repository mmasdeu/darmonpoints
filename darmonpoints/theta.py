from ast import In
from copy import copy, deepcopy
from itertools import chain
from warnings import warn

from sage.categories.groups import Groups
from sage.functions.generalized import sgn
from sage.groups.matrix_gps.linear import GL
from sage.matrix.matrix_space import MatrixSpace
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex
from sage.misc.verbose import verbose
from sage.modules.module import Module
from sage.rings.integer_ring import Z as ZZ
from sage.rings.integer_ring import IntegerRing
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


# Evaluate the rational function phi_D at z,
# where phi_D has divisor D and is normalized so that phi_D(oo) = 1
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
    if fails != 0:
        warn('Fails in eval_rat: %s' % fails)
    return ans

def pair_divisors(D1, D2):
    ans = 1
    for P, n in D1:
        for Q, m in D2:
            if P is Infinity or Q is Infinity:
                continue
            b = P - Q
            if b == 0:
                continue
            ans *= b**(m*n)
    return ans
 
def eval_rat_dlog(D, z):
    ans = 0
    fails = 0
    for P, n in D:
        if P is Infinity:
            continue
        zP = z - P
        if zP == 0:
            fails += n
        else:
            zPinv = ~zP
            ans += ZZ(n) * zPinv
    if fails != 0:
        warn('Fails in eval_rat_dlog: %s' % fails)
    return ans

def eval_rat_derivative(D, z, return_value=False):
    ans = 0
    ans0 = 1
    fails = 0
    for P, n in D:
        if P is Infinity:
            continue
        zP = z - P
        if zP == 0:
            fails += n
        else:
            zPinv = ~zP
            zPn = zP**ZZ(n) if n > 0 else zPinv**ZZ(-n)
            ans0 *= zPn
            ans += ZZ(n) * zPinv
        
    if fails != 0:
        warn('Fails in eval_rat_derivative: %s' % fails)
    if return_value:
        return ans0 * ans, ans0
    else:
        return ans0 * ans


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
        # self.m = 1
        self.z = K["z"].gen()
        self.MM = MeromorphicFunctions(self.K, self.p, self.prec)
        params = G.parameters
        gens_ext = G.gens_extended()
        
        # Corresponding to words of length exactly 1
        D1dict = {i : g * D for i, g in gens_ext}

        # Corresponding to words of length exactly 2
        verbose("Computing F2", level=2)
        self.F2 = { i :
            self.MM(sum(g * val for j, val in D1dict.items() if j != -i), tau)
                for (i, g), tau in zip(gens_ext, params)}
        verbose("F2 computed", level=2)
        
        # self.val will contain the 0, 1 terms
        self.val = sum(D1dict.values(), D)
        initial_F = kwargs.get('initial_F', None)
        if initial_F is not None:
            self.Fnlist = [{i : self.MM(initial_F[i], tau) for (i, _), tau in zip(gens_ext, params)}]
        else:
            self.Fnlist = [deepcopy(self.F2)]

    def improve(self, m, **kwargs):
        gens_ext = self.G.gens_extended()
        params = self.G.parameters
        # Initialize action_data
        verbose("Initializing action_data", level=2)
        action_data = {}
        for (i, gi), tau in zip(gens_ext, params):
            for j, Fj in self.Fnlist[-1].items():
                if i != -j:
                    action_data[i, j] = (
                        self.MM.get_action_data(gi, Fj._parameter, tau),
                        tau,
                    )
        verbose("action_data initialized", level=2)
        implementation = kwargs.get('implementation', 'list')
        if implementation not in ['list', 'fixedpoint']:
            raise ValueError("implementation must be 'list' or 'fixedpoint'")

        for it in range(m):
            # Stop if we reach the maximum precision
            # if self.m >= self.prec:
            #     break
            # Compute the next term from the last on in Fnlist            
            tmp = {}
            for (i, gi), tau in zip(gens_ext, params):
                for j, Fj in self.Fnlist[-1].items():
                    if i != -j:
                        vl = Fj.fast_act(action_data[i, j])
                        # vl = Fj.left_act_by_matrix(gi, tau)
                        try:
                            tmp[i] += vl
                        except KeyError:
                            tmp[i] = vl
            
            if implementation == 'list':
                # Append the new term
                self.Fnlist.append(tmp)
            else:
                # Add the new term to F2:
                verbose("Adding new term to F2", level=2)
                self.Fnlist = [{i : tmp[i] + self.F2[i] for i in tmp}]
                verbose('F2 updated', level=2)
            
            # self.m += 1
        
        # Collapse the list to one term and return
        if len(self.Fnlist) > 1:
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
        return f"Θ(z;{a},{b})"

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
        return f"\\Theta(z;{latex(a)},{latex(b)})"

    def __call__(self, z, **kwargs):
        return self.evaluate(z, **kwargs)

    def evaluate(self, z, **kwargs):
        if not isinstance(z, DivisorsElement):
            z = self.Div([(1, z)])
        if z.degree() != 0:
            z -= self.Div([(z.degree(), Infinity)])
        z = self.G.find_equivalent_divisor(z)
        ans0 = pair_divisors(self.val, z)
        prec = kwargs.get('prec', None)
        ans1 = prod(F.evaluate(z, prec) for FF in self.Fnlist for F in FF.values())
        return ans0 * ans1

    def eval_derivative(self, z, return_value=False):
        r'''
        EXAMPLES::
            sage: from darmonpoints.schottky import *
            sage: p = 3
            sage: prec = 10
            sage: working_prec = 200
            sage: K = Qp(p,working_prec)
            sage: h1 = matrix(K, 2, 2, [-5,32,-8,35])
            sage: h2 = matrix(K, 2, 2, [-13,80,-8,43])
            sage: G = SchottkyGroup(K, (h1,h2))
            sage: theta = G.theta(10, 7, 9)
            sage: theta.eval_derivative(13)
            2*3 + 3^2 + 2*3^6 + 3^7 + O(3^9)

        '''
        dlog = self.eval_dlog(z)
        z0 = self.G.to_fundamental_domain(z)[0]
        value = self.evaluate(z0)
        if return_value:
            return value * dlog, value
        else:
            return value * dlog

    def eval_dlog(self, z):
        if isinstance(z, DivisorsElement):
            raise NotImplementedError
        if not self.G.in_fundamental_domain(z):
            raise ValueError("z must be in the fundamental domain of G")
        z0, wd = self.G.to_fundamental_domain(z)
        if len(wd) > 0:
            gens = self.G.gens_extended(as_dict=True)
            g = prod((gens[i] for i in wd), gens[1].parent()(1)).adjugate()
            a, b, c, d = g.list()
            fact = (a * d - b * c) * (c * z + d) ** -2
        else:
            fact = 1
        valdlog = eval_rat_dlog(self.val, z0) # takes time
        fdlog = sum((f.eval_dlog(z0) for FF in self.Fnlist for f in FF.values()), valdlog) # takes time
        ans = fact * fdlog
        return ans
