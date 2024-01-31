######################
##                  ##
##    COHOMOLOGY    ##
##                  ##
######################
import operator
import os
from collections import defaultdict
from itertools import chain, groupby, islice, product, starmap, tee

from sage.algebras.group_algebra import GroupAlgebra
from sage.categories.action import Action
from sage.categories.homset import Hom
from sage.groups.group import AlgebraicGroup
from sage.matrix.constructor import Matrix, block_matrix, column_matrix, matrix
from sage.matrix.matrix_space import MatrixSpace
from sage.misc.cachefunc import cached_method
from sage.misc.lazy_attribute import lazy_attribute
from sage.misc.misc_c import prod
from sage.misc.persist import db, db_save
from sage.misc.verbose import verbose
from sage.modules.free_module_element import free_module_element, vector
from sage.modules.module import Module
from sage.parallel.decorate import fork, parallel
from sage.rings.all import (
    RR,
    ComplexField,
    LaurentSeriesRing,
    PolynomialRing,
    Qp,
    QuadraticField,
    RealField,
    Zmod,
    Zp,
)
from sage.rings.number_field.number_field import NumberField
from sage.rings.padics.precision_error import PrecisionError
from sage.structure.element import ModuleElement, MultiplicativeGroupElement
from sage.structure.parent import Parent
from sage.structure.sage_object import SageObject, load, save

from .util import *


class CohomologyElement(ModuleElement):
    def __init__(self, parent, data):
        r"""
        Define an element of `H^1(G,V)`

        INPUT:
            - G: a BigArithGroup
            - V: a CoeffModule
            - data: a list

        TESTS::

            sage: from darmonpoints.sarithgroup import BigArithGroup
            sage: from darmonpoints.cohomology_arithmetic import ArithCoh
            sage: G = BigArithGroup(5,6,1,use_shapiro=False,outfile='/tmp/darmonpoints.tmp') #  optional - magma
            sage: Coh = ArithCoh(G) #  optional - magma
            sage: 2 in Coh.hecke_matrix(13).eigenvalues() #  optional - magma
            True
            sage: -4 in Coh.hecke_matrix(7).eigenvalues() #  optional - magma
            True
            sage: PhiE = Coh.gen(1) #  optional - magma
        """
        G = parent.group()
        V = parent.coefficient_module()
        if isinstance(data, list):
            self._val = [V(o) for o in data]
        elif hasattr(data, "evaluate"):
            self._val = [V(data.evaluate(b)) for b in G.gens()]
        else:
            try:
                self._val = [V(data(b)) for b in G.gens()]
            except TypeError:
                # Assume constant cocycle
                self._val = [V(data) for b in G.gens()]
        ModuleElement.__init__(self, parent)

    def _evaluate_word_tietze(self, word, left_act_by=None):
        if self.parent()._trivial_action:
            return self._evaluate_word_tietze_trivial(tuple(word))
        elif self.parent()._acting_matrix is None:
            return self._evaluate_word_tietze_naive(
                tuple(word), left_act_by=left_act_by
            )
        else:
            return self._evaluate_word_tietze_foxgradient(
                tuple(word), left_act_by=left_act_by
            )

    def values(self):
        return self._val

    def _vector_(self, R=None):
        ambient = self.parent().space()
        ans = vector(sum([list(o) for o in self._val], []))
        return ambient(ambient.V()(ans))

    def _repr_(self):
        return "Cohomology class in %s" % self.parent()

    def _add_(self, right):
        return self.__class__(
            self.parent(), [a + b for a, b in zip(self._val, right._val)]
        )

    def _sub_(self, right):
        return self.__class__(
            self.parent(), [a - b for a, b in zip(self._val, right._val)]
        )

    def _neg_(self):
        return self.__class__(self.parent(), [-a for a in self._val])

    def _div_(self, right):
        ans = None
        for u, v in zip(self.values(), right.values()):
            if v != 0:
                try:
                    ans = u / v
                    break
                except (IndexError, ZeroDivisionError):
                    pass
        if ans is None:
            raise RuntimeError("It seems that we are trying to divide by 0")
        return ans

    def __rmul__(self, right):
        return self.__class__(self.parent(), [ZZ(right) * a for a in self._val])

    def is_zero(self):
        return self._vector_() == 0

    def valuation(self, p=None):
        try:
            return min([u.valuation(p) for u in self._val])
        except TypeError:
            return min([u.valuation() for u in self._val])

    def pair_with_cycle(self, xi):
        return sum(self.evaluate(g).pair_with(a) for g, a in xi)

    def evaluate(self, x, left_act_by=None, at_identity=False):
        H = self.parent()
        G = H.group()
        if x.parent() is G:
            wd = x.word_rep
        else:
            x = G(x)
            wd = x.word_rep
        if at_identity:
            return self._evaluate_word_tietze_identity(wd, left_act_by=left_act_by)
        else:
            return self._evaluate_word_tietze(wd, left_act_by=left_act_by)

    def check_cocycle_property(self, g1=None, g2=None, function=None):
        H = self.parent()
        G = H.group()
        if function is None:
            function = lambda x: x.is_zero()  # (x == 0)
        if function == -1:
            if g1 is None:
                return [(self._evaluate_word_tietze(r)) for r in G.get_relation_words()]
            else:
                return (
                    self.evaluate(g1 * g2) - self.evaluate(g1) - g1 * self.evaluate(g2)
                )
        else:
            if g1 is None:
                return all(
                    [
                        function(self._evaluate_word_tietze(r))
                        for r in G.get_relation_words()
                    ]
                )
            else:
                return function(
                    self.evaluate(g1 * g2) - self.evaluate(g1) - g1 * self.evaluate(g2)
                )

    def _evaluate_word_tietze_naive(self, word, left_act_by=None):
        G = self.parent().group()
        if len(word) == 0:
            return self.parent().coefficient_module()(0)
        g = word[0]
        if g > 0:
            ans = self._val[g - 1]
            gamma = G.gen(g - 1)
        else:
            g0 = -g - 1
            gamma = G.gen(g0) ** -1
            ans = -(gamma * self._val[g0])
        for g in word[1:]:
            if g > 0:
                ans += gamma * self._val[g - 1]
                gamma = gamma * G.gen(g - 1)
            else:
                g0 = -g - 1
                gamma = gamma * G.gen(g0) ** -1
                ans -= gamma * self._val[g0]
        return ans if left_act_by is None else left_act_by * ans

    def _evaluate_word_tietze_foxgradient(self, word, left_act_by=None):
        HH = self.parent()
        G = HH.group()
        V = HH.coefficient_module()

        if len(word) == 0:
            return V(0)
        R = V.base_ring()
        if hasattr(V, "dimension"):
            dim = V.dimension()
            MS = MatrixSpace(R, dim, dim)
        elif hasattr(V, "basis"):
            dim = len(V.basis())
            MS = MatrixSpace(R, dim, dim)
        else:
            MS = lambda x: x
        fgrad = HH.fox_gradient(tuple(word))
        if hasattr(self._val[0], "_moments"):
            ff = lambda v: v._moments.lift()
        elif hasattr(self._val[0], "_vector_"):
            ff = lambda v: v._vector_()
        else:
            ff = lambda v: v
        ans = sum(
            HH.GA_to_local(A, left_act_by) * ff(val) for A, val in zip(fgrad, self._val)
        )
        return V(ans)

    def _evaluate_word_tietze_identity(self, word, left_act_by=None):
        if self.parent()._trivial_action:
            return self._evaluate_word_tietze_trivial_identity(word)

        G = self.parent().group()
        V = self.parent().coefficient_module()

        if len(word) == 0:
            return V(0)[0]
        g = word[0]
        if g > 0:
            ans = self._val[g - 1][0]
            gamma = G.gen(g - 1)
        else:
            g0 = -g - 1
            gamma = G.gen(g0) ** -1
            ans = -self._val[g0].act_and_evaluate_at_identity(gamma)
        for g in word[1:]:
            if g > 0:
                ans += self._val[g - 1].act_and_evaluate_at_identity(gamma)
                gamma = gamma * G.gen(g - 1)
            else:
                g0 = -g - 1
                gamma = gamma * G.gen(g0) ** -1
                ans -= self._val[g0].act_and_evaluate_at_identity(gamma)
        return ans if left_act_by is None else left_act_by * ans

    def _evaluate_word_tietze_trivial(self, word):
        return sum(
            (self._val[g - 1] if g > 0 else -self._val[-g - 1] for g in word),
            self.parent().coefficient_module()(0),
        )

    def _evaluate_word_tietze_trivial_identity(self, word):
        return sum(
            (self._val[g - 1][0] if g > 0 else -self._val[-g - 1][0] for g in word),
            self.parent().coefficient_module()(0)[0],
        )


class CohomologyGroup(Module):
    Element = CohomologyElement

    def __init__(self, G, V, action_map=None, **kwargs):
        self._group = G
        self._coeffmodule = V
        onemat = G(1)
        self._gen_pows = []
        self._gen_pows_neg = []
        self._trivial_action = kwargs.get("trivial_action", False)
        if action_map is None:
            if hasattr(V, "dimension"):
                self._acting_matrix = lambda x, y: matrix(
                    V.base_ring(), V.dimension(), V.dimension(), 1
                )
            else:
                self._acting_matrix = None
        else:
            action = ArithAction(G, V, action_map)
            V._unset_coercions_used()
            V.register_action(action)

        if hasattr(V, "acting_matrix"):
            self._acting_matrix = lambda x, y: V.acting_matrix(x, y)
        gens_local = [(g, g**-1) for g in G.gens()]
        GA = GroupAlgebra(G)
        self._GA = GA
        for g, ginv in gens_local:
            self._gen_pows.append([GA(G(1)), GA(g)])
            self._gen_pows_neg.append([GA(G(1)), GA(ginv)])
        Module.__init__(self, base=ZZ)
        return

    @cached_method
    def generator_acting_matrix(self, g):
        V = self.coefficient_module()
        if hasattr(V, "dimension"):
            dim = V.dimension()
        elif hasattr(V, "basis"):
            dim = len(V.basis())
        else:
            dim = None
        return self._acting_matrix(g, dim)

    def GA_to_local(self, x, g0=None):
        if g0 is None:
            return sum(
                (
                    a * self.generator_acting_matrix(g.support()[0])
                    for a, g in zip(x.coefficients(), x.monomials())
                )
            )
        else:
            return self.generator_acting_matrix(g0) * sum(
                (
                    a * self.generator_acting_matrix(g.support()[0])
                    for a, g in zip(x.coefficients(), x.monomials())
                )
            )

    def group(self):
        return self._group

    def coefficient_module(self):
        return self._coeffmodule

    @cached_method
    def space(self):
        r"""
        Calculates the space of cocyles modulo coboundaries, as a Z-module.

        TESTS:

        sage: from darmonpoints.sarithgroup import *
        sage: from darmonpoints.cohomology_abstract import *
        sage: from darmonpoints.ocmodule import *
        sage: GS = BigArithGroup(5, 6,1,use_shapiro=False,outfile='/tmp/darmonpoints.tmp') #  optional - magma
        sage: G = GS.large_group() #  optional - magma
        sage: V = OCVn(5,1)     #  optional - magma
        sage: Coh = CohomologyGroup(G,V) #  optional - magma
        """
        verb = get_verbose()
        set_verbose(0)
        V = self.coefficient_module()
        R = V.base_ring()
        Vdim = V.dimension()
        G = self.group()
        gens = G.gens()
        ambient = R ** (Vdim * len(gens))
        # Now find the subspace of cocycles
        A = Matrix(R, Vdim * len(gens), 0)
        for nr, r in enumerate(G.get_relation_words()):
            set_verbose(verb)
            verbose("Processing relation word %s" % nr)
            set_verbose(0)
            Alist = [
                MatrixSpace(R, Vdim, Vdim)(self.GA_to_local(o))
                for o in self.fox_gradient(tuple(r))
            ]
            newA = block_matrix(Alist, nrows=1)
            A = A.augment(newA.transpose())
        A = A.transpose()
        cocycles = ambient.submodule(
            [ambient(o) for o in A.right_kernel_matrix().rows()]
        )
        gmat = block_matrix(
            [self._acting_matrix(g, Vdim) - 1 for g in G.gens()], nrows=len(G.gens())
        )
        coboundaries = cocycles.submodule([ambient(o) for o in gmat.columns()])
        ans = cocycles.quotient(coboundaries)
        set_verbose(verb)
        return ans

    @cached_method
    def dimension(self):
        try:
            return len([o for o in self.space().invariants() if o == 0])
        except AttributeError:
            return self.space().rank()

    def zero(self):
        return self.element_class(
            self, [self._coeffmodule(0) for g in range(len(self.group().gens()))]
        )

    def _an_element_(self):
        return self.zero()

    def _element_constructor_(self, x):
        return self.element_class(self, x)

    def _coerce_map_from_(self, S):
        if isinstance(S, CohomologyGroup):
            return True
        else:
            return False

    @cached_method
    def gen(self, i):
        vi = self.space().gen(i)
        try:
            vi = vi.lift()
        except AttributeError:
            pass
        vi = list(vi)
        V = self.coefficient_module()
        Vdim = V.dimension()
        data = []
        for i in range(0, len(vi), Vdim):
            data.append(V(vi[i : i + Vdim]))
        return self.element_class(self, data)

    def gens(self):
        return [self.gen(i) for i in range(self.dimension())]

    def _repr_(self):
        return "H^1(G,V), with G being %s and V = %s" % (
            self.group(),
            self.coefficient_module(),
        )

    @cached_method
    def fox_gradient(self, word, red=None):
        if red is None:
            red = lambda x: x
        V = self.coefficient_module()
        h = self.get_gen_pow(0, 0, red)
        ans = [self._gen_pows[0][0].parent()(0) for o in self.group().gens()]
        if len(word) == 0:
            return ans
        word = tietze_to_syllables(word)
        lenword = len(word)
        for j in range(lenword):
            i, a = word[j]
            ans[i] += h * self.get_fox_term(i, a, red)
            ans[i] = red(ans[i])
            if j < lenword - 1:
                h = red(h * self.get_gen_pow(i, a, red))
        return ans

    def get_gen_pow(self, i, a, red=None):
        if red is None:
            red = lambda x: x
        if a == 0:
            return self._gen_pows[0][0]
        elif a > 0:
            genpows = self._gen_pows[i]
        else:
            genpows = self._gen_pows_neg[i]
            a = -a
        while len(genpows) <= a:
            tmp = genpows[1] * genpows[-1]
            genpows.append(red(tmp))
        return genpows[a]

    def get_fox_term(self, i, a, red=None):
        if red is None:
            red = lambda x: x
        if a == 1:
            return self._gen_pows[i][0]
        elif a == -1:
            return -self._gen_pows_neg[i][1]
        elif a > 1:
            genpows = self._gen_pows[i]
            ans = genpows[0] + genpows[1]
            for o in range(a - 2):
                ans = red(ans)
                ans = genpows[0] + genpows[1] * ans
            return red(ans)
        elif a < -1:
            a = -a
            genpows = self._gen_pows_neg[i]
            ans = genpows[0] + genpows[1]
            for o in range(a - 2):
                ans = red(ans)
                ans = genpows[0] + genpows[1] * ans
            ans = -genpows[1] * ans
            return red(ans)

    def eval_at_genpow(self, i, a, v, red=None):
        if red is None:
            red = lambda x: x
        V = v._val[i].parent()
        v = v._val[i]._val
        if a == 1:
            return V(v)
        elif a == -1:
            return V(-(self._gen_pows_neg[i][1] * v))
        elif a > 1:
            genpows = self._gen_pows[i]
            ans = V(v + genpows[1] * v)
            for o in range(a - 2):
                ans.reduce_mod()
                ans = V(v) + V(genpows[1] * ans._val)
            return ans.reduce_mod()
        elif a < -1:
            a = -a
            genpows = self._gen_pows_neg[i]
            ans = V(v) + V(genpows[1] * v)
            for o in range(a - 2):
                ans.reduce_mod()
                ans = V(v) + V(genpows[1] * ans._val)
            ans = V(-genpows[1] * ans._val)
            return ans.reduce_mod()

    @cached_method
    def hecke_matrix(self, l, use_magma=True, g0=None):  # l can be oo
        dim = self.dimension()
        R = self.coefficient_module().base_ring()
        M = matrix(R, dim, dim, 0)
        for j, cocycle in enumerate(self.gens()):
            # Construct column j of the matrix
            verbose(
                "Constructing column %s/%s of the hecke matrix for prime %s"
                % (j, dim, l)
            )
            fvals = self.apply_hecke_operator(cocycle, l, use_magma=use_magma, g0=g0)
            M.set_column(j, list(vector(fvals)))
        return M
