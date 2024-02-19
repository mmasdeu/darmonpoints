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
from .theta import *

infinity = Infinity


def find_midpoint(K, v0, v1):
    t = K(v0.a - v1.a).valuation()
    if t < v0.r_valuation and t < v1.r_valuation:
        distance = (v0.r_valuation - t) + (v1.r_valuation - t)
    else:
        distance = abs(v0.r_valuation - v1.r_valuation)
    v, comp = (v1, False) if v1.r_valuation > v0.r_valuation else (v0, True)
    return Balls(K)(
        v.a, v.r_valuation - QQ(distance) / 2, is_open=not comp, is_complement=comp
    )


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

class SchottkyGroup_abstract(SageObject):
    def __init__(self, K, generators):
        self.K = K
        self.pi = K.uniformizer()
        self._generators = tuple([o.change_ring(K) for o in generators])
        self._inverse_generators = tuple(~v for v in self._generators)
        self._G = Groups().free(len(generators))

    def base_ring(self):
        return self.K

    def base_field(self):
        return self.K

    def uniformizer(self):
        return self.pi

    def element_to_matrix(self, gamma):
        ans = self._G(gamma)(self._generators)
        ans.set_immutable()
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
        return "Schottky group with %s generators" % len(self.generators())

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
        if z is Infinity:
            return 1
        if gamma is not None:
            if b != ZZ(1):
                raise ValueError("If gamma is specified, then b should not")
            b = act(gamma, a)
        K = z.parent()
        max_length = kwargs.pop("max_length", -1)
        num = K(1)
        den = K(1)
        can_stop = False
        for i in NN:
            new_num = K(1)
            new_den = K(1)
            if max_length == -1:
                can_stop = True
            for _, g in self.enumerate_group_elements(i):
                ga = act(g, a)
                tmp1 = K(1) if ga is Infinity else z - K(ga)
                gb = act(g, b)
                tmp2 = K(1) if gb is Infinity else z - K(gb)
                new_num *= tmp1
                new_den *= tmp2
                val = (tmp1 / tmp2 - K(1)).valuation()
                if val < m - tmp1.valuation():
                    can_stop = False
            num *= new_num
            den *= new_den
            if can_stop or i == max_length:
                break
        return num / den

    def theta_derivative_naive(self, m, a, b, z=None, max_length=-1, base_field=None, s=None):
        if s is not None:
            A = self.theta_naive(m,a,b,z=z,max_length=max_length,base_field=base_field)
            B = self.theta_naive(m,act(s,a),act(s,b),z=z,max_length=max_length,base_field=base_field)
            Ap = self.theta_derivative_naive(m,a,b,z=z,max_length=max_length,base_field=base_field,s=None)
            Bp = self.theta_derivative_naive(m,act(s,a),act(s,b),z=z,max_length=max_length,base_field=base_field,s=None)
            return Ap*B + A * Bp

        num = 1
        den = 1

        second_term = 0
        old_ans = 1
        val = 0
        for i in NN:
            verbose(f'{i = }')
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
            if i == max_length or (i > 0 and val >= (new_ans / old_ans -1).valuation()):
                break
            old_ans = new_ans
            val = (new_ans / old_ans -1).valuation()
        return new_ans.add_bigoh(val+new_ans.valuation())

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
                for h in [g, ~g]:
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

    def construct_tree(self, level):
        g0 = self._generators[0]
        b0, b1 = find_eigenvector_matrix(g0).column(0)
        base = b0 / b1
        T = NeighborJoiningTree(
            self.K, [act(g, base) for wd, g in self.all_elements_up_to_length(level)]
        )
        if level == 1:
            pp = [choose_leaf(tt) for tt in T.tree[1][:2]]
            self.root_vertex = T.BT([T.root, *pp])
        self.NJtree = T
        self._action_table = None
        return self.NJtree

    @cached_method
    def fundamental_domain(self, level=1, check=True):
        while True:
            level += 1
            verbose(f"Trying {level = }")
            self.construct_tree(level)
            try:
                return self._fundamental_domain(check=check)
            except ValueError as e:
                verbose(str(e))

    def _fundamental_domain(self, i0=None, check=True):
        tree = self.NJtree
        if i0 is None:
            i0 = tree.vertex_index(self.root_vertex)
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
        verts = self.NJtree.vertices()
        for i, (e0, e1, word) in enumerate(pairing):
            w = self._G.one()
            for l in word:
                w = w * (self._G.gen(l // 2) ** ((-1) ** l))
            good_generators.append(w)
            B0 = find_midpoint(self.K, verts[e0[0]], verts[e0[1]])
            B1 = find_midpoint(self.K, verts[e1[0]], verts[e1[1]])
            balls[i + 1] = B1
            balls[-(i + 1)] = B0
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
        edges = set()
        for i in range(n_vertices):
            for j in adj[i]:
                edges.add((i, j))
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
    def __init__(self, K, generators, balls=None,  transformation=None, keep_generators=True, check=False):
        if balls is None:
            G = PreSchottkyGroup(K, generators)
            gp = G.group()
            good_gens, good_balls, _ = G.fundamental_domain()
            if all(len(o.Tietze()) == 1 for o in good_gens):
                self.balls = {}
                for j0, gg in enumerate(good_gens):
                    i = gg.Tietze()[0]
                    idx = sgn(i) * (j0 + 1)
                    self.balls[i] = good_balls[idx]
                    self.balls[-i] = good_balls[-idx]
                    self._transformation = [w for w in gp.gens()]
            else:
                if keep_generators:
                    raise ValueError("Generators are not in good position")
                else:
                    # print(good_gens)
                    generators = [G.element_to_matrix(g) for g in good_gens]
                    self.balls = good_balls
                    self._transformation = good_gens
        else:
            self.balls = balls
            self._transformation = transformation
        if check:
            test_fundamental_domain(generators, self.balls)
        super().__init__(K, generators)

    @cached_method
    def a_point(self, in_interior=True):
        K = self.base_ring()
        x = K.random_element()
        n_iters = 0
        while n_iters < 100:
            n_iters += 1
            try:
                x0 = self.to_fundamental_domain(x)[0]
                if in_interior:
                    if any(x0 in B.closure() for B in self.balls.values()):
                        raise ValueError
                return x0
            except ValueError:
                x = K.random_element()
        raise RuntimeError("Reached maximum iterations (100)")

    def find_point(self, gamma, eps=1, idx=None):
        balls = self.balls
        if idx is not None:
            B = balls[-idx]
            if idx > 0:
                assert self.generators()[idx-1] == gamma
            else:
                assert self.generators()[-idx-1]**-1 == gamma
        else:
            gens = [(i + 1, o) for i, o in enumerate(self.generators())]
            gens.extend([(-i, o.determinant() ** -1 * o.adjugate()) for i, o in gens])
            B = next(balls[-i] for i, g in gens if g == gamma)
        return B.center.lift_to_precision() + eps * self.pi ** ZZ(B.radius)

    def to_fundamental_domain(self, x):
        r"""
        Returns a point z in the closure of the fundamental domain
        and a word w = [i1,...,ik] (in Tietze notation)
        such that gi1 * ... * gik * z = x
        """
        gens = self.generators()
        inv_gens = self.inverse_generators()
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
        return x, word

    def in_fundamental_domain(self, x, strict=False):
        return self.in_which_ball(x, closure=strict) is None

    def word_problem(self, gamma):
        z0 = self.a_point()
        z1 = act(gamma, z0)
        z2, word = self.to_fundamental_domain(z1)
        if not z0.is_equal_to(z2, 10): # DEBUG
            gens = [(i + 1, o) for i, o in enumerate(self.generators())]
            gens.extend([(-i, o.determinant() ** -1 * o.adjugate()) for i, o in gens])
            found = False
            for i, g in gens:
                gz2 = act(g, z2)
                if z0.is_equal_to(gz2, 10):
                    word.append(i)
                    found = True
                    break
            if not found:
                raise RuntimeError(f"Something went wrong! {z0 = }, {z2 = } {word = }")
        return tuple(word)

    def matrix_to_element(self, g):
        return self._G(self.word_problem(g))

    def in_which_ball(self, x, closure=False):
        if closure:
            return next((i for i, B in self.balls.items() if x in B.closure()), None)
        else:
            return next((i for i, B in self.balls.items() if x in B), None)

    def find_equivalent_divisor(self, D):
        # Compute an equivalent divisor to D with proper support
        # We replace (a) with (a0) - (g z) + (z) for a0 and z in
        # the closure of the fundamental domain.
        p = self.pi
        gens = self.generators()
        balls = self.balls
        wd = [0 for _ in range(self.genus())]
        Div = D.parent()
        ans = Div([])
        for P, n in D:
            P0, new_wd = self.to_fundamental_domain(P)
            for i in new_wd:
                wd[abs(i) - 1] += n * sgn(i)
            ans += n * Div([(1,P0)])
        for i, (g, e) in enumerate(zip(gens, wd)):
            if e == 0:
                continue
            gamma = gens[i]
            zz = self.find_point(gamma)
            ans -= e * Div([(1,zz), (-1, act(gamma,zz))])
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
        gens = self.generators()
        if b is not None:
            try:
                K = a.parent()
            except AttributeError:
                K = self.base_ring()
            if K.is_exact(): # DEBUG, set to avoid 0 and 1...
                K = self.base_ring()
            DK = Divisors(K)
            D0 = DK([(1,a),(-1,b)])
        else:
            D0 = a
            try:
                K = a.parent().base_ring()
            except AttributeError:
                K = self.base_ring()
            if K.is_exact(): # DEBUG, set to avoid 0 and 1...
                K = self.base_ring()

        s = kwargs.pop("s", None)
        if s is not None:
            D0 += s * D0
        D = self.find_equivalent_divisor(D0)
        ans = ThetaOC(self, a=D, b=None, prec=prec, base_ring=K, **kwargs)
        z = kwargs.pop('z', None)
        improve = kwargs.pop("improve", True)
        if improve or z is not None:
            ans = ans.improve(prec)
        return ans if z is None else ans(z)

    @cached_method
    def u_function(self, gamma, prec, a=None, **kwargs):
        r"""
        Compute u_gamma
        """
        wd = self.word_problem(gamma)
        gens = self.generators()
        if len(wd) > 1:
            if kwargs.get('z', None) is None:
                raise NotImplementedError('Need to specify a point at which we will evaluate')
            return prod(self.u_function(gens[abs(i)-1], prec, a=a, **kwargs)**sgn(i) for i in wd)

        if a is None:
            a = self.find_point(gamma) # Should pass idx=wd[0] DEBUG ??
            assert self.in_fundamental_domain(a, strict=False)
            assert self.in_fundamental_domain(act(gamma, a), strict=False)
        K = a.parent()
        DK = Divisors(K)
        D = DK([(1,a), (-1, act(gamma, a))])
        ans = ThetaOC(self, a=D, b=None, prec=prec, base_ring=K, **kwargs)
        improve = kwargs.pop("improve", True)
        if improve:
            ans = ans.improve(prec)
        z = kwargs.pop('z', None)
        return ans if z is None else ans(z)

    @cached_method
    def period_matrix(self, prec, **kwargs):
        g = len(self.generators())
        M = MatrixSpace(self.base_ring(),g,g)(0)
        z1 = kwargs.get("z1", None)
        if z1 is None:
            z1 = self.a_point()
        for i in range(g):
            g1 = self.generators()[i]
            T = self.u_function(g1, prec, a=z1, **kwargs).improve(prec)
            for j in range(i, g):
                g2 = self.generators()[j]
                z2 = kwargs.get("z2", None)
                if z2 is None:
                    z2 = self.find_point(g2, eps=1 + self.pi)
                g2_z2 = act(g2, z2)
                num = T(z2, recursive=False)
                den = T(g2_z2, recursive=False)
                M[i,j] = num / den
                M[j,i] = num / den
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
        g = len(self.generators())
        if i in ZZ:
            assert j in ZZ
            g1 = self.generators()[i]
            g2 = self.generators()[j]
        else:
            a = word_to_abelian(i, g)
            b = word_to_abelian(j, g)
            m = self.period_matrix(prec, **kwargs)
            return a * m * b

        z1 = kwargs.pop("z1", None)
        if z1 is None:
            z1 = self.a_point()
        z2 = kwargs.pop("z2", None)
        if z2 is None:
            z2 = self.find_point(g2, eps=1 + self.pi)
        g2_z2 = act(g2, z2)
        T = self.u_function(g1, prec, a=z1, **kwargs).improve(prec)
        num = T(z2, recursive=False)
        den = T(g2_z2, recursive=False)
        verbose(f"{num = }")
        verbose(f"{den = }")
        return num / den

    def period_naive(self, i, j, prec, **kwargs):
        g1 = self.generators()[i]
        g2 = self.generators()[j]
        z1 = self.find_point(g1)
        if i == j:
            z1 = act(g1.adjugate(), z1)
            z2 = self.find_point(g2, eps=self.pi + 1)
        else:
            z2 = self.find_point(g2)
        num = self.theta_naive(prec, z=z2, a=z1, gamma=g1, **kwargs)
        den = self.theta_naive(prec, z=act(g2, z2), a=z1, gamma=g1, **kwargs)
        verbose(f"{num = }")
        verbose(f"{den = }")
        return num / den


class Ball(Element):
    def __init__(self, parent, center, radius, is_open=True, is_complement=False):
        self.radius = radius
        self.center = parent.K(center).add_bigoh(self.radius + 1)
        self.is_complement = is_complement
        self.is_open = is_open
        Element.__init__(self, parent)

    def _repr_(self):
        p = self.parent().K.prime()
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
        if not (
            self.radius == other.radius
            and self.is_open == other.is_open
            and self.is_complement == other.is_complement
        ):
            return False
        if self.is_complement:
            return self.complement() == other.complement()
        else:
            return self.center in other and other.center in self

    def __ne__(self, other):
        return not self == other

    def _acted_upon_(self, g, on_left):
        # If oo \notin g(B(x,r)), then g(B(x,r)) = B(gx, r.|g'(x)|)
        # (here, g'(x) = (det(g)) / (cx+d)^2)
        # If oo \in g(B(x,r)), then g(B(x,r)) = P1 - B(g(oo), 1/r . |g'(x)|)
        # (here, g'(x) = det(g) / c^2
        # We do have to check these formulas, especially the x that appears
        # in P1 - B(g(oo), 1/r . |g'(x)|)
        C = self.__class__
        if hasattr(g, "matrix"):
            g = g.matrix()
        a, b, c, d = g.list()
        x = self.center
        x = x.lift_to_precision()
        try:
            if (-d / c - x).valuation() > self.radius:
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

    def __init__(self, K):
        self.K = K
        Parent.__init__(self)

    def _repr_(self):
        return "Set of balls for P^1(K), with K = " + str(self.K)

    def _element_constructor_(self, center, radius, is_open=True, is_complement=False):
        return self.element_class(self, center, radius, is_open, is_complement)


class BTVertex(ModuleElement):
    def __init__(self, parent, a, r_valuation):
        KK = parent.base_ring()
        try:
            ln = len(a)
            ps = [KK(i) for i in a if i is not Infinity]
            if len(ps) == 2:
                self.r_valuation = (ps[0] - ps[1]).valuation()
                self.a = ps[0].add_bigoh(self.r_valuation)
            else:
                d12 = (ps[0] - ps[1]).valuation()
                d23 = (ps[1] - ps[2]).valuation()
                d13 = (ps[0] - ps[2]).valuation()
                maxval = max([d12, d23, d13])
                self.r_valuation = maxval
                self.a = (
                    ps[0].add_bigoh(maxval) if d12 == maxval or d13 == maxval else ps[1]
                )
        except TypeError:
            try:
                self.r_valuation = ZZ(r_valuation)
                self.a = KK(a).add_bigoh(r_valuation)
            except TypeError:
                self.r_valuation = Infinity
                self.a = KK(a)
        ModuleElement.__init__(self, parent)

    def contained_in(self, other):
        return (self.a - other.a).valuation() <= other.r_valuation

    def __hash__(self):
        return hash(self.get_key())

    @cached_method
    def is_zero(self):
        return self.a.is_zero(self.r_valuation)

    @cached_method
    def get_key(self):
        return (
            self.r_valuation
            if self.is_zero()
            else (self.a.add_bigoh(self.r_valuation), self.r_valuation)
        )

    def _repr_(self):
        return f"Ball({self.a},|π|^{self.r_valuation})"

    def __eq__(self, other):
        return self.get_key() == other.get_key()

    def _add_(self, other):
        C = self.__class__
        return C(
            self.parent(), self.a + other.a, min(self.r_valuation, other.r_valuation)
        )

    def _lmul_(self, b):
        C = self.__class__
        KK = self.parent().base_ring()
        assert b != 0
        return C(self.parent(), self.a * b, self.r_valuation + KK(b).valuation())

    def inv(self):
        C = self.__class__
        if self.is_zero():
            return C(self.parent(), 0, -self.r_valuation)
        else:
            return C(
                self.parent(), 1 / self.a, self.r_valuation - 2 * self.a.valuation()
            )

    def _acted_upon_(self, g, on_left):
        if hasattr(g, "matrix"):
            g = g.matrix()
        if g[1, 0] == 0:
            return 1 / g[1, 1] * (g[0, 0] * self + g[0, 1])
        else:
            t = (g[1, 0] * self + g[1, 1]).inv()
            r = (g[0, 1] - g[0, 0] * g[1, 1] / g[1, 0]) * t + g[0, 0] / g[1, 0]
            return r


class BTTree(UniqueRepresentation, Module):
    Element = BTVertex

    def __init__(self, K):
        self.prec = K.precision_cap()
        Module.__init__(self, base=K)

    def _element_constructor_(self, a, rval=None):
        if rval is None:
            rval = Infinity
        return self.element_class(self, a, rval)

    def _an_element_(self):
        return self.element_class(self, 1, 2)

    def _coerce_map_from_(self, S):
        if self.base().has_coerce_map_from(S):
            return True


def four_point_configuration(K, pts):
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
        self.BT = BTTree(self.K)
        leaves = uniq(leaves)
        self.root = leaves[0]
        self.tree = [Infinity, [[None, leaves[1]], [None, leaves[2]]]]
        self.leaves = leaves
        self._adjacency_list = None
        for leaf in leaves[3:]:
            self.add_leaf(leaf)
        self.update_vertex_table()

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
        if not leaf(subtree):
            p1 = choose_leaf(subtree[1][0])
            p2 = choose_leaf(subtree[1][1])
            return sum(
                (self.vertices(tt) for tt in subtree[1]), [self.BT([self.root, p1, p2])]
            )
        else:
            return []

    def vertex_index(self, v0, subtree=None):
        return next((i for i, v in enumerate(self.vertices(subtree)) if v == v0))

    def update_vertex_table(self):
        self.vertex_table = {hash_vertex(v): i for i, v in enumerate(self.vertices())}

    def adjacency_list(self):
        if self._adjacency_list is not None:
            return self._adjacency_list
        r = tuple([] for _ in self.vertices())
        for v1, v2 in self.adjacency():
            try:
                i1 = self.vertex_table[hash_vertex(v1)]
            except KeyError:
                i1 = self.vertices().index(v1)
            try:
                i2 = self.vertex_table[hash_vertex(v2)]
            except KeyError:
                i2 = self.vertices().index(v2)
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
            v = self.BT([self.root, p1, p2])
            result = [[root, v]] if root is not None and not leaf(subtree) else []
            return sum((self.adjacency(tt, v) for tt in subtree[1]), result)
        else:
            return []


def test_fundamental_domain(gens, balls):
    all_gens = [(i + 1, g) for i, g in enumerate(gens)] + [
        (-(i + 1), g**-1) for i, g in enumerate(gens)
    ]
    fails = []
    for i, g in all_gens:
        for j, _ in all_gens:
            if i == j:
                continue
            if (balls[i].closure()).intersects(balls[j].closure()):
                fails.append((i, j))
                verbose(f"Test *failed* for balls {i = } and {j = }")
            else:
                verbose(f"Test passed for balls {i = } and {j = }")
        if g * balls[-i].complement() != balls[i].closure():
            fails.append(i)
            verbose(f"Test *failed* for {i = }")
        else:
            verbose(f"Test passed for {i = }")
    if len(fails) > 0:
        raise RuntimeError(f"Some tests failed. ({fails})")
