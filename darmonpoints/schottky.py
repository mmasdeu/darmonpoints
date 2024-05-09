from copy import copy, deepcopy
from itertools import chain

from sage.categories.groups import Groups
from sage.combinat.rooted_tree import LabelledRootedTree as LTR
from sage.functions.generalized import sgn
from sage.graphs.graph import Graph
from sage.groups.matrix_gps.linear import GL
from sage.matrix.constructor import Matrix
from sage.matrix.matrix_space import MatrixSpace
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex
from sage.misc.lazy_attribute import lazy_attribute
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
from .theta import *
from .util import muted

infinity = Infinity


def reduce_word(w):
    r = []
    for i in w:
        if len(r) == 0:
            r.append(i)
        else:
            if i != r[-1] and i // 2 == r[-1] // 2:
                r.pop()
            else:
                r.append(i)
    return tuple(r)


def invert_word(w):
    return tuple([i + (-1) ** i for i in reversed(w)])


def enumerate_group_elements(gens, invgens, length):
    if length == 0:
        yield [], gens[0].parent().one()
    elif length == 1:
        for i, (v, vinv) in enumerate(zip(gens, invgens)):
            yield [i + 1], v
            yield [-i - 1], vinv
    else:
        for wd, g in enumerate_group_elements(gens, invgens, length - 1):
            for i, (v, vinv) in enumerate(zip(gens, invgens)):
                if wd[-1] != -(i + 1):
                    yield wd + [i + 1], g * v
                if wd[-1] != i + 1:
                    yield wd + [-i - 1], g * vinv


def all_elements_up_to_length(gens, invgens, N):
    return chain(*[enumerate_group_elements(gens, invgens, i) for i in range(N + 1)])


def hash_vertex(v):
    try:
        return hash(v)
    except:
        return hash(str(v))


def uniq(lst):
    ans = []
    for o in lst:
        if o not in ans:
            ans.append(o)
    return ans


@muted
@cached_function
def find_eigenvector_matrix(g):
    t = g.trace()
    n = g.determinant()
    delta = (t * t - 4 * n).sqrt()
    vaps = sorted([(t + delta) / 2, (t - delta) / 2], key=lambda o: o.valuation())
    veps = sum(((g - l).right_kernel().basis() for l in vaps), [])
    return g.matrix_space()(veps).transpose()


@cached_function
def find_parameter(g, ball, pi=None, check=True):
    if pi is None:
        pi = g.parent().base_ring().uniformizer()
    g = g.apply_map(lambda o: o.lift_to_precision())
    ans = copy(find_eigenvector_matrix(g).adjugate())
    r = ball.radius
    # column 0 means that the boundary of B_g (the ball attached to g)
    # gets sent to the circle of radius 1.
    # Concretely, if B_g = B(a, p^-r), we send a+p^r |-> 1.
    # As a consequence, P^1-B_g gets sent to the closed ball B(0,1).
    z0 = ball.center.lift_to_precision() + pi ** ZZ(r)
    if check:
        assert z0 in ball.closure() and z0 not in ball
    lam = (ans[0, 0] * z0 + ans[0, 1]) / (ans[1, 0] * z0 + ans[1, 1])
    ans.rescale_row(0, 1 / lam)
    ans.set_immutable()
    if check:
        if act(ans, z0) != 1:
            raise RuntimeError
        # if ans * ball.complement() != ball.parent()(0, 0).closure():
        #     # print(ans * ball.complement())
        #     # print(ball.parent()(0,0).closure())
        #     raise RuntimeError
    return ans


@cached_function
def find_parameter_new(g, ball, pi=None, check=True):
    K = g.parent().base_ring()
    if pi is None:
        pi = K.uniformizer()
    g = g.apply_map(lambda o: o.lift_to_precision())
    r = ball.radius
    z0 = ball.center.lift_to_precision()
    if ball.is_complement:
        ans = Matrix(K, 2, 2, [0, 1, 1, -z0])
    else:
        ans = Matrix(K, 2, 2, [1, -z0, 0, 1])
    return ans


class SchottkyGroup_abstract(SageObject):
    def __init__(self, K, generators):
        self.K = K
        self.pi = K.uniformizer()
        self._generators = tuple([o.change_ring(K) for o in generators])
        self._inverse_generators = tuple(v.adjugate() for v in self._generators)
        self._G = Groups().free(len(generators))

    def base_ring(self):
        return self.K

    def base_field(self):
        return self.K

    def uniformizer(self):
        return self.pi

    @muted
    def element_to_matrix(self, gamma):
        verb_level = get_verbose()
        set_verbose(0)
        ans = self._G(gamma)(self._generators)
        ans.set_immutable()
        set_verbose(verb_level)
        return ans

    def group(self):
        return self._G

    def genus(self):
        return len(self._generators)

    def generators(self):
        return self._generators

    def inverse_generators(self):
        return self._inverse_generators

    def _repr_(self):
        return "Schottky group with %s generators" % len(self._generators)

    def enumerate_group_elements(self, length):
        return enumerate_group_elements(
            self._generators, self._inverse_generators, length
        )

    def all_elements_up_to_length(self, N):
        return chain(
            *[
                enumerate_group_elements(self._generators, self._inverse_generators, i)
                for i in range(N + 1)
            ]
        )

    def theta_naive(self, m, a=ZZ(0), b=ZZ(1), z=None, gamma=None, **kwargs):
        K = self.K
        if z is Infinity:
            return K(1)
        if gamma is not None:
            if b != ZZ(1):
                raise ValueError("If gamma is specified, then b should not")
            b = act(gamma, a)
        max_length = kwargs.pop("max_length", -1)
        num = K(1)
        den = K(1)
        can_stop = False
        for i in NN:
            new_num = K(1)
            new_den = K(1)
            if i > 2 and max_length == -1:
                can_stop = True
            for _, g in self.enumerate_group_elements(i):
                ga = act(g, a)
                tmp1 = K(1) if ga is Infinity else z - ga
                gb = act(g, b)
                tmp2 = K(1) if gb is Infinity else z - gb
                new_num *= tmp1
                new_den *= tmp2
                try:
                    val = (tmp1 / tmp2 - 1).valuation()
                    tmp1val = tmp1.valuation()
                except TypeError:
                    val = -Infinity
                    tmp1val = 0
                if val < m - tmp1val:
                    can_stop = False
            num *= new_num
            den *= new_den
            if can_stop or i == max_length:
                break
        return num / den

    def theta_derivative_naive(
        self, m, a, b, z=None, max_length=-1, base_field=None, s=None
    ):
        if s is not None:
            A = self.theta_naive(
                m, a, b, z=z, max_length=max_length, base_field=base_field
            )
            B = self.theta_naive(
                m,
                act(s, a),
                act(s, b),
                z=z,
                max_length=max_length,
                base_field=base_field,
            )
            Ap = self.theta_derivative_naive(
                m, a, b, z=z, max_length=max_length, base_field=base_field, s=None
            )
            Bp = self.theta_derivative_naive(
                m,
                act(s, a),
                act(s, b),
                z=z,
                max_length=max_length,
                base_field=base_field,
                s=None,
            )
            return Ap * B + A * Bp

        num = 1
        den = 1

        second_term = 0
        old_ans = 1
        val = 0
        for i in NN:
            verbose(f"{i = }")
            for _, g in self.enumerate_group_elements(i):
                ga = act(g, a)
                gb = act(g, b)
                new_num = z - ga
                new_den = z - gb
                num *= new_num
                den *= new_den
                new_second_term = (ga - gb) / (new_num * new_den)
                second_term += new_second_term
            new_ans = (num / den) * second_term
            if i == max_length or (
                i > 0 and val >= (new_ans / old_ans - 1).valuation()
            ):
                break
            old_ans = new_ans
            val = (new_ans / old_ans - 1).valuation()
        return new_ans.add_bigoh(val + new_ans.valuation())


class PreSchottkyGroup(SchottkyGroup_abstract):
    def __init__(self, K, generators):
        self._action_table = None
        self.pi = K.uniformizer()
        super().__init__(K, generators)
        self.construct_tree(1)

    def action_table(self):
        if self._action_table is None:
            self._action_table = []
            VT = self.NJtree.vertex_table
            for g in self._generators:
                for h in [g, g.adjugate()]:
                    new_list = []
                    for v in self.NJtree.vertices():
                        hv = h * v
                        idx = VT.get(hash_vertex(hv))
                        if idx is None:
                            try:
                                idx = self.NJtree.vertices().index(hv)
                            except ValueError:
                                idx = None
                        new_list.append(idx)
                    self._action_table.append(new_list)
        return self._action_table

    @lazy_attribute
    def base(self):
        for g in self._generators:
            try:
                b0, b1 = find_eigenvector_matrix(g).column(0)
                return b0 / b1
            except (ZeroDivisionError, NotImplementedError):
                pass
        raise RuntimeError("Base not found")

    def construct_tree(self, level):
        T = NeighborJoiningTree(
            self.K,
            [act(g, self.base) for wd, g in self.all_elements_up_to_length(level)],
        )
        if level == 1:
            pp = [choose_leaf(tt) for tt in T.tree[1][:2]]
            self.root_vertex = T.BT.vertex_from_three_points([T.root, *pp])
        self.NJtree = T
        self._action_table = None
        return self.NJtree

    @cached_method
    @muted
    def fundamental_domain(self, level=1, check=True):
        while True:
            level += 1
            verbose(f"Trying {level = }")
            self.construct_tree(level)
            try:
                return self._fundamental_domain(check=check)
            except ValueError as e:
                verbose(str(e))

    @muted
    def _fundamental_domain(self, i0=None, check=True):
        tree = self.NJtree
        if i0 is None:
            i0 = tree.vertices().index(self.root_vertex)
        adj = tree.adjacency_list()
        edge_classes = self.edge_classes()
        open_edges = [(None, i0)]
        pairing = []
        while len(open_edges) != 0:
            # print(f'{open_edges = }')
            cur0, cur1 = open_edges.pop(0)
            # print(f'{adj[cur1] = }')
            for i in adj[cur1]:
                if i != cur0:
                    nxt = (cur1, i)
                    found = False
                    tst = edge_classes[nxt][0]
                    for other in open_edges:
                        other_rev = (other[1], other[0])
                        if tst == edge_classes[other_rev][0]:
                            w = reduce_word(
                                edge_classes[other_rev][1]
                                + invert_word(edge_classes[nxt][1])
                            )
                            pairing.append((nxt, other, w))
                            found = True
                            break
                    if found:
                        open_edges.remove(other)
                    else:
                        open_edges.append(nxt)
        if check and not self.certify(pairing, i0):
            raise ValueError("Not a correct fundamental domain")
        good_generators = []
        balls = {}
        T = self.NJtree
        verts = T.vertices()
        mid = lambda x, y: T.BT.find_midpoint(x, y)
        for i, ((v00, v01), (v10, v11), word) in enumerate(pairing):
            w = self._G.one()
            for l in word:
                w = w * (self._G.gen(l // 2) ** ((-1) ** l))
            good_generators.append(w)
            g = self.element_to_matrix(w)
            B0 = mid(verts[v00], verts[v01])
            B1 = mid(verts[v10], verts[v11])
            if (
                verts[v00].radius == verts[v01].radius
                or verts[v10].radius == verts[v11].radius
            ):
                assert (
                    g * B0.complement() != B1.closure()
                    or g.adjugate() * B1.complement() != B0.closure()
                )
                B0 = mid(verts[v00], B0)
                B1 = (g * B0.closure()).complement()
            balls[i + 1] = B1
            balls[-(i + 1)] = B0
        if check:
            try:
                newgens = [self.element_to_matrix(o) for o in good_generators]
                test_fundamental_domain(newgens, balls)
            except RuntimeError:
                raise ValueError("Not a correct fundamental domain (test)")
        return good_generators, balls, pairing

    def certify(self, pairing, i0):
        genus = self.genus()
        if len(pairing) != genus:
            return False
        tree = self.NJtree
        action_table = self.action_table()
        edge_classes = self.edge_classes()
        subtrees = []
        subtrees_dict = {}
        for e1, e2, w in pairing:
            for T in tree.get_subtree(*e1):
                subtrees_dict[T] = (w, False)
            for T in tree.get_subtree(*e2):
                subtrees_dict[T] = (w, True)
        # print(f'{pairing = }')
        for act in action_table:
            gv = act[i0]
            if gv is None:
                return False
            while True:
                # print('certify')
                # print('gv', gv)
                try:
                    word, inv = subtrees_dict[gv]
                    wrev = (
                        tuple([i + (-1) ** i for i in word]) if inv else reversed(word)
                    )
                    for gi in wrev:
                        gv = action_table[gi][gv]
                        if gv is None:
                            return False
                except (StopIteration, KeyError):
                    if gv == i0:
                        break
                    else:
                        return False
        return True

    def vertex_classes(self):
        action_table = self.action_table()
        r = dict()
        visited = set()
        for i in range(len(action_table[0])):
            if not i in visited:
                visited.add(i)
                open_list = [(i, ())]
                r[i] = (i, ())
                while len(open_list) > 0:
                    current, current_word = open_list.pop()
                    for j, actj in enumerate(action_table):
                        nxt = actj[current]
                        if nxt is not None and not (nxt in visited):
                            next_word = reduce_word((j,) + current_word)
                            visited.add(nxt)
                            open_list.append((nxt, next_word))
                            r[nxt] = (i, next_word)
        return r

    def edge_classes(self, action_table=None):
        if action_table is None:
            action_table = self.action_table()
        adj = self.NJtree.adjacency_list()
        n_vertices = len(adj)
        edges = set(((i, j) for i in range(n_vertices) for j in adj[i]))
        r = dict()
        visited = set()
        for i in edges:
            if not i in visited:
                visited.add(i)
                open_list = [(i, ())]
                r[i] = (i, ())
                while len(open_list) > 0:
                    current, current_word = open_list[0]
                    open_list = open_list[1:]
                    for j, actj in enumerate(action_table):
                        nxt = (actj[current[0]], actj[current[1]])
                        if (nxt in edges) and not (nxt in visited):
                            next_word = reduce_word((j,) + current_word)
                            visited.add(nxt)
                            open_list.append((nxt, next_word))
                            r[nxt] = (i, next_word)
        return r

    def to_schottky(self):
        generators, balls, _ = self.fundamental_domain()
        return SchottkyGroup(self.K, generators, balls)


class SchottkyGroup(SchottkyGroup_abstract):
    def __init__(
        self,
        K,
        generators,
        balls=None,
        transformation=None,
        parameters=None,
        keep_generators=True,
        check=True,
    ):
        if balls is not None:
            self._balls = balls
        if transformation is not None:
            self._transformation = transformation
        if parameters is not None:
            self.parameters = parameters
        self._keep_generators = keep_generators
        super().__init__(K, generators)
        if check:
            self.test_fundamental_domain()

    def test_fundamental_domain(self):
        balls = self.balls()
        gens = self._generators
        test_fundamental_domain(gens, balls)

    def balls(self):
        try:
            return self._balls
        except AttributeError:
            pass
        K = self.base_ring()
        generators = self._generators
        G = PreSchottkyGroup(K, generators)
        gp = G.group()
        good_gens, good_balls, _ = G.fundamental_domain()
        if all(len(o.Tietze()) == 1 for o in good_gens):
            balls = {}
            for j0, gg in enumerate(good_gens):
                i = gg.Tietze()[0]
                idx = sgn(i) * (j0 + 1)
                balls[i] = good_balls[idx]
                balls[-i] = good_balls[-idx]
                self._transformation = [w for w in gp.gens()]
        else:
            if self._keep_generators:
                raise ValueError("Generators are not in good position")
            else:
                # print(good_gens)
                self._generators = [G.element_to_matrix(g) for g in good_gens]
                self._inverse_generators = tuple(
                    [o.adjugate() for o in self._generators]
                )
                balls = good_balls
                self._transformation = good_gens
        self._balls = balls
        return balls

    @cached_method
    def gens_extended(self):
        gens = [(i + 1, o) for i, o in enumerate(self._generators)]
        gens.extend([(-i, o.determinant() ** -1 * o.adjugate()) for i, o in gens])
        for i, o in gens:
            o.set_immutable()
        return gens

    @lazy_attribute
    def parameters(self):
        balls = self.balls()
        ans = [find_parameter(o, balls[i], self.pi) for i, o in self.gens_extended()]
        for t in ans:
            t.set_immutable()
        return ans

    def a_point(self):
        K = self.base_ring()
        n_iters = 0
        while n_iters < 100:
            n_iters += 1
            x = K.random_element()
            try:
                x0 = self.to_fundamental_domain(x)[0]
            except ValueError:
                continue
            if self.in_fundamental_domain(x0, strict=True):
                return x0
        raise RuntimeError("Reached maximum iterations (100)")

    def find_point(self, gamma, eps=1, idx=None):
        balls = self.balls()
        gens = self.gens_extended()
        if idx is not None:
            B = balls[-idx]
            if idx > 0:
                if self._generators[idx - 1] != gamma:
                    B1 = next(balls[-i] for i, g in gens if g == gamma)
                    # print(f'!! {B = } but {B1 = }')
                    # print(balls)
                    B = B1
            else:
                if self._generators[-idx - 1] ** -1 != gamma:
                    B1 = next(balls[-i] for i, g in gens if g == gamma)
                    # print(f'!! {B = } but {B1 = }')
                    # print(balls)
                    B = B1
        else:
            B = next(balls[-i] for i, g in gens if g == gamma)
        ans = B.center.lift_to_precision() + eps * self.pi ** ZZ(B.radius)
        test = lambda x: self.in_fundamental_domain(x, strict=False)

        try:
            if not test(ans):
                raise RuntimeError(
                    f"{ans = } should be in fundamental domain, but it is not."
                )
            ga = act(gamma, ans)
            if not test(ga):
                raise RuntimeError(
                    f"gamma * ans = {ga} should be in fundamental domain, but it is not."
                )
        except RuntimeError:
            new_idx = -idx if idx is not None else None
            ginv = gamma**-1
            ans = self.find_point(ginv, eps, new_idx)
            return act(ginv, ans)
        return ans

    def to_fundamental_domain(self, x):
        r"""
        Returns a point z in the closure of the fundamental domain
        and a word w = [i1,...,ik] (in Tietze notation)
        such that gi1 * ... * gik * z = x
        """
        gens = self._generators
        inv_gens = self._inverse_generators
        gens = [None] + list(gens) + list(reversed(inv_gens))
        word = []
        i = self.in_which_ball(x)
        while i is not None:
            word.append(i)
            x1 = act(gens[-i], x)
            if x1 == x:
                raise ValueError(
                    "x is a limit point, cannot be brought to fundamental domain"
                )
            x = x1
            i = self.in_which_ball(x)
        return x, tuple(word)

    def in_fundamental_domain(self, x, strict=False):
        return self.in_which_ball(x, closure=strict) is None

    def word_problem(self, gamma):
        found = False
        while not found:
            z0 = self.a_point()
            z1 = act(gamma, z0)
            z2, word = self.to_fundamental_domain(z1)
            if z0 == z2:
                found = True
                break
            else:  # DEBUG: why is this needed?
                gens = [(i + 1, o) for i, o in enumerate(self._generators)]
                gens.extend(
                    [(-i, o.determinant() ** -1 * o.adjugate()) for i, o in gens]
                )
                for i, g in gens:
                    gz2 = act(g, z2)
                    if z0 == gz2:
                        word.append(-i)
                        found = True
                        break
                # if not found:
                #     raise RuntimeError(f"Something went wrong! {z0 = }, {z2 = } {word = }")
        return tuple(word)

    @muted
    def matrix_to_element(self, g):
        return self._G(self.word_problem(g))

    def in_which_ball(self, x, closure=False):
        if closure:
            return next((i for i, B in self.balls().items() if x in B.closure()), None)
        else:
            return next((i for i, B in self.balls().items() if x in B), None)

    def find_equivalent_divisor(self, D):
        # Compute an equivalent divisor to D with proper support
        # We replace (a) with (a0) - (g z) + (z) for a0 and z in
        # the closure of the fundamental domain.
        p = self.pi
        gens = self._generators
        balls = self.balls()
        wd = [0 for _ in range(self.genus())]
        Div = D.parent()
        ans = Div([])
        for P, n in D:
            P0, new_wd = self.to_fundamental_domain(P)
            for i in new_wd:
                wd[abs(i) - 1] += n * sgn(i)
            ans += n * Div([(1, P0)])
        for i, (g, e) in enumerate(zip(gens, wd)):
            if e == 0:
                continue
            zz = self.find_point(g, idx=i + 1)
            ans -= e * Div([(1, zz), (-1, act(g, zz))])
        return ans

    def theta(self, prec, a, b=None, **kwargs):
        r"""
        Compute the Theta function

        EXAMPLES ::

        sage: from darmonpoints.schottky import *
        sage: p = 3
        sage: prec = 20
        sage: working_prec = 200
        sage: K = Qp(p,working_prec)
        sage: g1 = matrix(K, 2, 2, [-5,32,-8,35])
        sage: g2 = matrix(K, 2, 2, [-13,80,-8,43])
        sage: G = SchottkyGroup(K, (g1, g2))
        sage: a = 23
        sage: b = 14
        sage: z0 = K(8)
        sage: m = 10
        sage: Tg = G.theta_naive(m, z=z0, a=a,b=b)
        sage: T = G.theta(prec, a, b).improve(m)
        sage: (T(z0) / Tg - 1).valuation() > m
        True

        """
        K = self.base_ring()
        if b is not None:
            DK = Divisors(K)
            D0 = DK([(1, a), (-1, b)])
        else:
            D0 = a
        s = kwargs.pop("s", None)
        if s is not None:
            D0 += s * D0
        recursive = kwargs.get("recursive", True)
        if recursive:
            D0 = self.find_equivalent_divisor(D0)
        ans = ThetaOC(self, a=D0, b=None, prec=prec, base_ring=K, **kwargs)
        z = kwargs.pop("z", None)
        improve = kwargs.pop("improve", True)
        if improve or z is not None:
            ans = ans.improve(prec)
        return ans if z is None else ans(z)

    def u_function(self, gamma, prec, a=None, **kwargs):
        r"""
        Compute u_gamma
        """
        wd = self.word_problem(gamma)
        gens = self._generators
        z = kwargs.get("z", None)
        if len(wd) > 1 or wd[0] < 0:
            if z is None:
                kwargs.pop('z', None)
                return lambda z: prod(
                    self._u_function(gens[abs(i) - 1], prec, a=a)(z)
                    ** ZZ(sgn(i))
                    for i in wd
                )
            return prod(
                self._u_function(gens[abs(i) - 1], prec, a=a)(z) ** ZZ(sgn(i))
                for i in wd
            )
        if z is None:
            return lambda z : self._u_function(gens[wd[0] - 1], prec, a=a)(z)
        else:
            return self._u_function(gens[wd[0] - 1], prec, a=a)(z)


    @cached_method
    def _u_function(self, gamma, prec, a):
        r"""
        Compute u_gamma
        """
        wd = self.word_problem(gamma)
        gens = self._generators
        assert len(wd) == 1 and wd[0] > 0
        if a is None:
            a = self.find_point(gamma, idx=wd[0])
        K = a.parent()
        DK = Divisors(K)
        D = DK([(1, a), (-1, act(gamma, a))])
        ans = ThetaOC(self, a=D, b=None, prec=prec, base_ring=K)
        ans = ans.improve(prec)
        return ans

    @cached_method
    def period_matrix(self, prec, **kwargs):
        g = len(self._generators)
        M = MatrixSpace(self.base_ring(), g, g)(0)
        z1 = kwargs.get("z1", None)
        if z1 is None:
            z1 = self.a_point()
        for i in range(g):
            g1 = self._generators[i]
            T = self.u_function(g1, prec, a=z1, **kwargs)
            for j in range(i, g):
                g2 = self._generators[j]
                z2 = kwargs.get("z2", None)
                if z2 is None:
                    z2 = self.find_point(g2, eps=1 + self.pi)
                g2_z2 = act(g2, z2)
                num = T(z2)
                den = T(g2_z2)
                M[i, j] = num / den
                M[j, i] = num / den
        return M

    @cached_method
    def period(self, i, j, prec, **kwargs):
        r"""
        Compute the (i,j)-entry of the period matrix.

        EXAMPLES ::

        sage: from darmonpoints.schottky import *
        sage: p = 3
        sage: prec = 10
        sage: working_prec = 200
        sage: K = Qp(p,working_prec)
        sage: h1 = matrix(K, 2, 2, [-5,32,-8,35])
        sage: h2 = matrix(K, 2, 2, [-13,80,-8,43])
        sage: G = SchottkyGroup(K, (h1,h2))
        sage: q00g = G.period_naive(0, 0, prec)
        sage: q01g = G.period_naive(0, 1, prec)
        sage: q11g = G.period_naive(1, 1, prec)
        sage: q00 = G.period(0,0, prec)
        sage: q01 = G.period(0,1, prec)
        sage: q11 = G.period(1,1, prec)
        sage: (q00g/q00-1).valuation() > prec
        True
        sage: (q01g/q01-1).valuation() > prec
        True
        sage: (q11g/q11-1).valuation() > prec
        True
        """
        g = len(self._generators)
        if i in ZZ:
            assert j in ZZ
            g1 = self._generators[i]
            g2 = self._generators[j]
        else:
            ilist = i
            jlist = j
            m = self.period_matrix(prec, **kwargs)
            ans = m.parent().base_ring()(1)
            for i in ilist:
                i0, isgn = abs(i) - 1, sgn(i)
                for j in jlist:
                    j0, jsgn = abs(j) - 1, sgn(j)
                    ans *= m[i0, j0] ** ZZ(isgn * jsgn)
            return ans

        z1 = kwargs.pop("z1", None)
        if z1 is None:
            z1 = self.a_point()
        z2 = kwargs.pop("z2", None)
        if z2 is None:
            z2 = self.find_point(g2, eps=1 + self.pi, idx=j + 1)
        g2_z2 = act(g2, z2)
        T = self.u_function(g1, prec, a=z1, **kwargs)
        num = T(z2)
        den = T(g2_z2)
        verbose(f"{num = }")
        verbose(f"{den = }")
        return num / den

    def period_naive(self, i, j, prec, **kwargs):
        g1 = self._generators[i]
        g2 = self._generators[j]
        z1 = self.find_point(g1, idx=i + 1)
        if i == j:
            z1 = act(g1.adjugate(), z1)
            z2 = self.find_point(g2, eps=self.pi + 1, idx=j + 1)
        else:
            z2 = self.find_point(g2, idx=j + 1)
        num = self.theta_naive(prec, z=z2, a=z1, gamma=g1, **kwargs)
        den = self.theta_naive(prec, z=act(g2, z2), a=z1, gamma=g1, **kwargs)
        verbose(f"{num = }")
        verbose(f"{den = }")
        return num / den


class Ball(Element):
    def __init__(self, parent, center, radius, is_open=True, is_complement=False):
        self.radius = QQ(radius)
        self.center = parent.K(center).add_bigoh(ZZ(self.radius.ceil()) + 1)
        self.is_complement = is_complement
        self.is_open = is_open
        Element.__init__(self, parent)

    def __hash__(self):
        return hash(str(self.get_key()))

    @cached_method
    def get_key(self):
        r = self.radius
        return r if self.center.is_zero(r) else (self.center.add_bigoh(r), r)

    def _repr_(self):
        comp = "P^1 - " if self.is_complement else ""
        opn = "" if self.is_open else "+"
        return f"{comp}B({self.center},|π|^{self.radius}){opn}"

    def intersects(self, other):
        # We use the fact that two balls intersect iff they are concentric.
        return (self.center in other) or (other.center in self)

    def __contains__(self, b):
        if self.is_complement:
            return b not in self.complement()
        if b is Infinity:
            return False
        d = b - self.center
        if self.is_open:
            in_ball = d.valuation() > self.radius
        else:
            in_ball = d.valuation() >= self.radius
        return in_ball

    def complement(self):
        C = self.__class__
        return C(
            self.parent(),
            self.center,
            self.radius,
            self.is_open,
            not self.is_complement,
        )

    def closure(self):
        C = self.__class__
        is_open = bool(self.is_complement)
        return C(self.parent(), self.center, self.radius, is_open, self.is_complement)

    def interior(self):
        C = self.__class__
        is_open = not bool(self.is_complement)
        return C(self.parent(), self.center, self.radius, is_open, self.is_complement)

    def __eq__(self, other):
        return self.parent().are_equal(self, other)

    def __ne__(self, other):
        return not self == other

    def _acted_upon_(self, g, on_left):
        # If oo \notin g(B(x,r)), then g(B(x,r)) = B(gx, r.|g'(x)|)
        # (here, g'(x) = (det(g)) / (cx+d)^2)
        # If oo \in g(B(x,r)), then g(B(x,r)) = P1 - B(g(oo), 1/r . |g'(x)|)
        # (here, g'(x) = det(g) / c^2
        C = self.__class__
        if hasattr(g, "matrix"):
            g = g.matrix()
        a, b, c, d = g.list()
        x = self.center
        x = x.lift_to_precision()
        if self.is_open:
            try:
                if (x + d / c).valuation() > self.radius:
                    inf_in_image = True
                else:
                    inf_in_image = False
            except ZeroDivisionError:
                inf_in_image = False
        else:
            try:
                if (x + d / c).valuation() >= self.radius:
                    inf_in_image = True
                else:
                    inf_in_image = False
            except ZeroDivisionError:
                inf_in_image = False

        if inf_in_image:
            gpx = (g.determinant() / c**2).valuation()
            radius = -self.radius + gpx
            center = a / c
            is_comp = not self.is_complement
            is_open = not self.is_open
        else:
            gpx = (g.determinant() / (c * x + d) ** 2).valuation()
            radius = self.radius + gpx
            center = (a * x + b) / (c * x + d)
            is_comp = self.is_complement
            is_open = self.is_open

        return C(self.parent(), center, radius, is_open, is_comp)


class Balls(UniqueRepresentation, Parent):
    Element = Ball

    def __init__(self, K, oriented=True):
        self.K = K
        self._oriented = oriented
        Parent.__init__(self)

    def base_ring(self):
        return self.K

    def _repr_(self):
        return "Set of balls for P^1(K), with K = " + str(self.K)

    def _element_constructor_(self, center, radius, is_open=True, is_complement=False):
        if not self._oriented:
            is_open = False
            is_complement = False
        return self.element_class(self, center, radius, is_open, is_complement)

    def are_equal(self, left, right):
        if self._oriented:
            if not (
                left.radius == right.radius
                and left.is_open == right.is_open
                and left.is_complement == right.is_complement
            ):
                return False
            if left.is_complement:
                return left.complement() == right.complement()
            else:
                return left.center in right and right.center in left
        else:
            return (
                left.radius == right.radius
                and (left.center - right.center).valuation() >= left.radius
            )

    def find_midpoint(self, v0, v1):
        K = self.base_ring()
        t = K(v0.center - v1.center).valuation()
        if t < v0.radius and t < v1.radius:
            distance = (v0.radius - t) + (v1.radius - t)
        else:
            distance = abs(v0.radius - v1.radius)
        v, comp = (v1, False) if v1.radius > v0.radius else (v0, True)
        BK = Balls(K)
        return BK(
            v.center, v.radius - QQ(distance) / 2, is_open=not comp, is_complement=comp
        )

    def vertex_from_three_points(self, a):
        KK = self.base_ring()
        ln = len(a)
        ps = [KK(i) for i in a if i is not Infinity]
        if len(ps) == 2:
            val = (ps[0] - ps[1]).valuation()
            return self.element_class(self, ps[0].add_bigoh(val), val)
        else:
            assert len(ps) == 3
            d12 = (ps[0] - ps[1]).valuation()
            d23 = (ps[1] - ps[2]).valuation()
            d13 = (ps[0] - ps[2]).valuation()
            maxval = max([d12, d23, d13])
            center = (
                ps[0].add_bigoh(maxval) if d12 == maxval or d13 == maxval else ps[1]
            )
            return self.element_class(self, center, maxval)


def cross_ratio(points):
    [p1, p2, p3, p4] = points
    if p1 is Infinity:
        return (p3 - p2) / (p4 - p2)
    elif p2 is Infinity:
        return (p3 - p1) / (p4 - p1)
    elif p3 is Infinity:
        return (p4 - p2) / (p4 - p1)
    elif p4 is Infinity:
        return (p3 - p1) / (p3 - p2)
    else:
        return (p3 - p1) * (p4 - p2) / ((p4 - p1) * (p3 - p2))


def four_point_configuration(K, pts):
    p1, p2, p3, p4 = pts
    v1 = abs(K(cross_ratio([p1, p2, p3, p4])).valuation())
    v2 = abs(K(cross_ratio([p1, p3, p2, p4])).valuation())
    v3 = abs(K(cross_ratio([p1, p4, p2, p3])).valuation())
    if v2 > 0 and v3 > 0:
        return p3, v2
    elif v1 > 0 and v3 > 0:
        return p2, v1
    elif v1 > 0 and v2 > 0:
        return p1, v1
    else:
        return None, 0


def four_point_configuration_works(K, pts):
    V = [[K(pi - pj).valuation() for pj in pts] for pi in pts]
    v2 = abs(V[0][1] + V[2][3] - V[1][2] - V[0][3])
    v3 = abs(V[0][1] + V[2][3] - V[1][3] - V[0][2])
    if v2 > 0 and v3 > 0:
        return pts[2], v2
    v1 = abs(V[0][2] + V[1][3] - V[1][2] - V[0][3])
    if v1 > 0 and v3 > 0:
        return pts[1], v1
    elif v1 > 0 and v2 > 0:
        return pts[0], v1
    else:
        return None, 0


leaf = lambda t: t[0] is None


def choose_leaf(tree):
    while not leaf(tree):
        tree = tree[1][0]
    return tree[1]


class NeighborJoiningTree(SageObject):
    def __init__(self, K, leaves):
        self.K = K
        self.BT = Balls(self.K, oriented=False)
        leaves = uniq(leaves)
        self.root = leaves[0]
        self.tree = [Infinity, [[None, leaves[1]], [None, leaves[2]]]]
        self.leaves = leaves
        self._adjacency_list = None
        for leaf in leaves[3:]:
            self.add_leaf(leaf)
        self.update_vertex_table()

    def to_graph(self):
        tree = self.tree
        G = Graph(weighted=True)
        G.add_vertex(0)
        V = [(0, tt) for tt in tree[1]]
        W = []
        newlabel = 0
        Gdict = {}
        while len(V) > 0:
            for label, T in V:
                newlabel += 1
                G.add_vertex(newlabel)
                if leaf(T):
                    G.add_edge(label, newlabel, label=str(T[1].add_bigoh(3)))
                    Gdict[newlabel] = T[1]
                else:
                    G.add_edge(label, newlabel, label=str(T[0]))
                    W.extend([(newlabel, tt) for tt in T[1]])
            V = W
            W = []
        return G, Gdict

    def to_string(self, subtree):
        s = "--(" + str(subtree[0]) + ")--"
        if not leaf(subtree):
            s += "[" + str([self.to_string(tt) for tt in subtree[1]])[1:-1] + "]"
        else:
            s += str(subtree[1])
        return s

    def _repr_(self):
        return str(self.root) + self.to_string(self.tree)

    def get_subtree(self, v1, v2):
        adj = self.adjacency_list()
        visited = set([v2])
        open_list = []
        for i in adj[v2]:
            if i != v1:
                visited.add(i)
                open_list.append(i)
        while len(open_list) > 0:
            current = open_list.pop()
            for i in adj[current]:
                if not i in visited:
                    visited.add(i)
                    open_list.append(i)
        return visited

    def add_leaf(self, new_leaf, subtree=None):
        if subtree is None:
            subtree = self.tree
        K = self.K
        root = self.root
        l0 = choose_leaf(subtree[1][0])
        J = (
            (tt, four_point_configuration(K, [l0, choose_leaf(tt), root, new_leaf]))
            for tt in subtree[1][1:]
        )
        try:
            tt, (l1, length) = next((tt, (p, l)) for (tt, (p, l)) in J if p is not None)
        except StopIteration:
            subtree[1].append([None, new_leaf])
            return
        if l1 == root:
            subtree[1] = [[None, new_leaf], [length, subtree[1]]]
            subtree[0] = subtree[0] - length
        else:
            next_subtree = subtree[1][0] if l1 == l0 else tt
            if not leaf(next_subtree):
                self.add_leaf(new_leaf, next_subtree)
            else:
                lf = next_subtree[1]
                next_subtree[0] = length
                next_subtree[1] = [[None, new_leaf], [None, lf]]

    def vertices(self, subtree=None):
        if subtree is None:
            subtree = self.tree
        if leaf(subtree):
            return []
        children = subtree[1]
        p0 = choose_leaf(children[0])
        p1 = choose_leaf(children[1])
        V = [self.BT.vertex_from_three_points([self.root, p0, p1])]
        for tt in children:
            V.extend(self.vertices(tt))
        return V

    def update_vertex_table(self):
        self.vertex_table = {hash_vertex(v): i for i, v in enumerate(self.vertices())}

    def adjacency_list(self):
        if self._adjacency_list is not None:
            return self._adjacency_list
        r = tuple([] for _ in self.vertices())
        for v1, v2 in self.adjacency():
            i1 = self.vertex_table[hash_vertex(v1)]
            i2 = self.vertex_table[hash_vertex(v2)]
            r[i1].append(i2)
            r[i2].append(i1)
        self._adjacency_list = r
        return r

    def adjacency(self, subtree=None, root=None):
        self._adjacency_list = None
        if subtree is None:
            subtree = self.tree
        if not leaf(subtree):
            p1 = choose_leaf(subtree[1][0])
            p2 = choose_leaf(subtree[1][1])
            v = self.BT.vertex_from_three_points([self.root, p1, p2])
            result = [[root, v]] if root is not None and not leaf(subtree) else []
            return sum((self.adjacency(tt, v) for tt in subtree[1]), result)
        else:
            return []


def test_fundamental_domain(gens, balls):
    all_gens = [(i + 1, g) for i, g in enumerate(gens)] + [
        (-(i + 1), g.adjugate()) for i, g in enumerate(gens)
    ]
    fails = []
    for i, g in all_gens:
        for j, _ in all_gens:
            if i == j:
                continue
            if (balls[i].closure()).intersects(balls[j].closure()):
                fails.append(
                    (
                        i,
                        j,
                    )
                )
            #     verbose(f"Test *failed* for balls {i = } and {j = }")
            # else:
            #     verbose(f"Test passed for balls {i = } and {j = }")
        B0 = g * balls[-i].complement()
        B1 = balls[i].closure()
        if B0 != B1:
            fails.append(i)
        #     verbose(f"Test *failed* for {i = }. {B0 = }, {B1 = }")
        # else:
        #     verbose(f"Test passed for {i = }")
    if len(fails) > 0:
        raise RuntimeError(f"Some tests failed. ({fails})")
