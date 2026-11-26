r'''
Additive version of ThetaOC.

The multiplicative implementation (ThetaOC) represents the theta function on
each ball by power series F_i(t) with F_i(0) = 1, and improves them with
products of power series. Here we store log F_i instead, so that products
become sums.

This is possible because all the series F_i are principal units: they are
products of factors (1 - x t) with |x| < 1 (the points of their divisors lie
in the interior of the balls, and the parameters send the complement of the
ball to the closed unit disk). So log F_i converges on the closed unit disk,
and composing with the action of the group (the matrices of get_action_data)
commutes with taking logarithms. The normalization F_i(0) = 1 becomes
log F_i(0) = 0.

What is not a principal unit is the finite rational part coming from the
words of length at most 1 (self.val). For it we compute, multiplicatively,
only the valuation and the first p-adic digit, which is then lifted with the
Teichmuller character. The rest (principal units) is again computed with
logarithms. Altogether, a value of theta is obtained as

    Theta(z) = pi^v * teichmuller(d) * exp(L),

where v and d (a residue field element) are computed multiplicatively and L
additively. This needs exp and log to be inverse isomorphisms between the
principal units and the maximal ideal, that is e < p - 1.

The generic tools (log-series, p-adic logarithms and exponentials, and the
iteration with integer matrices) are in the meromorphic module.
'''
from copy import copy

from sage.misc.misc_c import prod
from sage.misc.verbose import verbose
from sage.modules.free_module_element import free_module_element as vector
from sage.rings.infinity import Infinity
from sage.structure.sage_object import SageObject

from .divisors import Divisors, DivisorsElement
# Some of these are not used here, but they used to be defined in this module
from .meromorphic import (
    LogSeries,
    LogSeriesOperator,
    MeromorphicFunctions,
    _check_integral,
    _coordinate_moebius_entries,
    _coordinates,
    _from_coordinates,
    _integer_moebius_matrix,
    _IntegerOperator,
    _integral_basis,
    _integral_moebius_coefficients,
    _inverse_integers,
    _ok_coordinates,
    _OKCoordinates,
    _PrecisionTracker,
    _ramification_data,
    _reduce_columns,
    _to_integer,
    evalpoly,
    exp_small,
    log_principal,
    log_series_of_divisor,
    principal_part_log,
)
from .theta import eval_rat_dlog, pair_divisors


class ThetaOCAdditive(SageObject):
    r'''
    Additive version of ThetaOC (see the module documentation).

    The interface is the same as that of ThetaOC (including initial_F, which
    is here a dictionary of lists of coefficients of log F_i (or of LogSeries,
    such as the Fnlist[-1] of a previous ThetaOCAdditive), and improve with
    tol), and evaluate returns the same values. evaluate_log returns the
    triple (v, d, L) such that the value is pi^v * teichmuller(d) * exp(L).
    '''
    def __init__(self, G, a=None, b=None, prec=None, **kwargs):
        K = kwargs.get("base_ring", None)
        if K is None:
            K = G.K
        self.K = K
        self.G = G
        self.p = G.pi
        p, e = _ramification_data(K)
        if e >= p - 1:
            raise NotImplementedError('The additive implementation needs e < p - 1')
        self.q = K.residue_field().cardinality()
        _ = G.generators()
        _ = G.balls()
        if prec is None:
            prec = K.precision_cap()
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
        # Only used to get the action data
        self.MM = MeromorphicFunctions(self.K, self.p, self.prec)
        params = G.parameters
        gens_ext = G.gens_extended()

        # Corresponding to words of length exactly 1
        D1dict = {i : g * D for i, g in gens_ext}

        # Corresponding to words of length exactly 2
        verbose("Computing L2", level=2)
        self.F2 = {i : LogSeries(log_series_of_divisor(sum(g * val for j, val in D1dict.items() if j != -i), tau, prec), tau)
                   for (i, g), tau in zip(gens_ext, params)}
        verbose("L2 computed", level=2)

        # self.val will contain the 0, 1 terms
        self.val = sum(D1dict.values(), D)
        initial_F = kwargs.get('initial_F', None)
        if initial_F is not None:
            self.Fnlist = [{i : LogSeries(self._to_vector(initial_F[i]), tau)
                            for (i, _), tau in zip(gens_ext, params)}]
        else:
            self.Fnlist = [copy(self.F2)]
        # How to compute the products with integer matrices (see _IntegerOperator)
        self._integral_mode = kwargs.get('integral_mode', None)  # None: default_integer_mode()
        # Last term of the list implementation (None means Fnlist[-1]). Since
        # improve collapses Fnlist into its sum, it is needed to continue the
        # iteration in a later call to improve.
        self._last_term = None

    def _to_vector(self, data):
        K = self.K
        if isinstance(data, LogSeries):
            # e.g. Fnlist[-1] of a previous theta, as for ThetaOC
            data = data._value
        data = [K(o) for o in list(data)[:self.prec]]
        data += [K(0)] * (self.prec - len(data))
        data[0] = K(0)
        return vector(K, [o.add_bigoh(self.prec) for o in data])

    def _get_action_data(self):
        try:
            return self._action_data
        except AttributeError:
            pass
        gens_ext = self.G.gens_extended()
        params = self.G.parameters
        action_data = {}
        for (i, gi), tau in zip(gens_ext, params):
            for j, Fj in self.Fnlist[-1].items():
                if i != -j:
                    action_data[i, j] = (
                        self.MM.compute_action_data(gi, Fj._parameter, tau),
                        tau,
                    )
        self._action_data = action_data
        return action_data

    def _integral_data(self):
        r'''
        When all the data (the coefficients of the Mobius transformations of
        the action, and the series in F2) is integral, return what is needed
        to do the iteration with integer matrices (which is much faster than
        with generic matrices over K): the keys, the series length P, the
        iteration operator (see LogSeriesOperator), and the vector of F2 with
        the precisions of its coefficients. Otherwise return None.
        '''
        try:
            return self._integral
        except AttributeError:
            pass
        try:
            self._integral = self._build_integral_data()
        except (TypeError, ValueError, ArithmeticError, NotImplementedError) as e:
            verbose(f'Not using integer matrices: {e}', level=2)
            self._integral = None
        return self._integral

    def _build_integral_data(self):
        K = self.K
        keys = list(self.F2.keys())
        P = self.prec
        # The Mobius transformations of the action (see get_action_data):
        # new_i = sum_{j != -i} F_j o zz_ij, where zz_ij = (b1 + a1 t) / (1 + c1 t)
        # with a1, b1 and c1 integral.
        gens = dict(self.G.gens_extended())
        params = {i : F._parameter for i, F in self.F2.items()}
        terms = {}
        for bi, i in enumerate(keys):
            for bj, j in enumerate(keys):
                if i == -j:
                    continue
                tau = params[i].change_ring(K)
                abcd = (params[j] * (tau * gens[i]).adjugate()).list()
                terms[bj, bi] = [(1, _integral_moebius_coefficients(abcd))]
        series = [o for i in keys for o in self.F2[i]._value]
        _check_integral(series)
        op = LogSeriesOperator(K, P, len(keys), terms, mode=self._integral_mode)
        return (keys, P, op, op.to_vector(series), op.initial_precisions(series))

    def _improve_integral(self, m, implementation, tol, data):
        r'''
        Same as improve, using integer matrices (see _integral_data). Return
        False if it cannot be used for the current approximation.
        '''
        import numpy as np
        keys, P, op, L2, L2prec = data
        N = P
        if implementation == 'list' and self._last_term is not None:
            source = self._last_term
        else:
            source = self.Fnlist[-1]
        current = [o for i in keys for o in source[i]._value]
        summed = [o for i in keys for o in self.Fnlist[0][i]._value]
        try:
            _check_integral(current + summed)
        except ValueError:
            return False
        # We compute modulo pi^N (lifting the inputs), and keep track of the
        # precision of each coefficient as the p-adic elements would (see
        # LogSeriesOperator.propagate).
        prec_v = op.initial_precisions(current)
        prec_total = op.initial_precisions(summed)
        # If all the inputs are known modulo pi^N, so are all the results
        tracking = min(int(prec_v.min()), int(prec_total.min()), op.min_input_prec, int(L2prec.min())) < N
        def propagate(precs, w):
            if not tracking:
                return precs
            return op.propagate(precs, w)
        def to_series(w, precs):
            return {i : LogSeries(value, self.F2[i]._parameter) for i, value in zip(keys, op.to_values(w, precs))}
        reduce, apply, add, sub, size = op.reduce, op.apply, op.add, op.sub, op.valuation
        v = op.to_vector(current)
        total = op.to_vector(summed)
        self.last_change = None
        best = None
        stalled = 0
        for _ in range(m):
            if implementation == 'list':
                prec_v = propagate(prec_v, v)
                prec_total = np.minimum(prec_total, prec_v)
                v = reduce(apply(v))
                total = add(total, v)
                change = size(v)
                done = not any(v) # All the remaining terms vanish too
            else:
                prec_v = np.minimum(propagate(prec_v, v), L2prec)
                w = reduce(add(L2, apply(v)))
                change = size(sub(w, v))
                done = (w == v) # Fixed point reached
                v = w
            self.last_change = change
            if done:
                break
            if tol is not None:
                if best is None or change > best:
                    best = change
                    stalled = 0
                else:
                    stalled += 1
                if change >= tol or stalled >= 2:
                    break
        if implementation == 'list':
            self._last_term = to_series(v, prec_v)
            self.Fnlist = [to_series(reduce(total), prec_total)]
        else:
            self._last_term = None
            self.Fnlist = [to_series(v, prec_v)]
        return True

    def improve(self, m, **kwargs):
        r'''
        Same as ThetaOC.improve. In addition, it stops as soon as the
        iteration is exactly done (the new term of the list implementation is
        zero, or the fixed point iteration does not change anything).

        The keyword integral (True by default) selects whether to do the
        iteration with integer matrices when possible (see _integral_data),
        which is much faster: in our tests, from 2 to 15 times for Qp,
        unramified extensions and Eisenstein extensions of both.
        '''
        gens_ext = self.G.gens_extended()
        implementation = kwargs.get('implementation', 'list')
        tol = kwargs.get('tol', None)
        if implementation not in ['list', 'fixedpoint']:
            raise ValueError("implementation must be 'list' or 'fixedpoint'")
        if len(self.Fnlist) == 1 and kwargs.get('integral', True):
            data = self._integral_data()
            if data is not None and self._improve_integral(m, implementation, tol, data):
                return self
        action_data = self._get_action_data()
        prec = self.prec
        self.last_change = None
        best = None
        stalled = 0
        if implementation == 'list' and self._last_term is not None:
            source = self._last_term
        else:
            source = self.Fnlist[-1]
        for _ in range(m):
            tmp = {}
            for i, _ in gens_ext:
                vl = sum(Fj._value * action_data[i, j][0]
                         for j, Fj in source.items() if i != -j)
                vl[0] = 0
                tmp[i] = vector(self.K, [o.add_bigoh(prec) for o in vl])
            if implementation == 'list':
                new = {i : LogSeries(v, self.F2[i]._parameter) for i, v in tmp.items()}
                self.Fnlist.append(new)
                source = new
                change = min(min(o.valuation() for o in v) for v in tmp.values())
                # All the remaining terms vanish too
                done = all(o.is_zero() for v in tmp.values() for o in v)
            else:
                new = {i : LogSeries(tmp[i] + self.F2[i]._value, self.F2[i]._parameter) for i in tmp}
                old = self.Fnlist[-1]
                diffs = [new[i]._value - old[i]._value for i in new]
                change = min(min(o.valuation() for o in v) for v in diffs)
                # Fixed point reached
                done = all(o.is_zero() for v in diffs for o in v)
                self.Fnlist = [new]
                source = new
            self.last_change = change
            if done:
                break
            if tol is not None:
                if best is None or change > best:
                    best = change
                    stalled = 0
                else:
                    stalled += 1
                if change >= tol or stalled >= 2:
                    break
        self._last_term = source if implementation == 'list' else None
        if len(self.Fnlist) > 1:
            self.Fnlist = [{ky : LogSeries(sum((F[ky]._value for F in self.Fnlist[1:]), self.Fnlist[0][ky]._value),
                                           self.Fnlist[0][ky]._parameter)
                            for ky in self.Fnlist[0]}]
        return self

    def _prepare_divisor(self, z):
        if not isinstance(z, DivisorsElement):
            z = self.Div([(1, z)])
        if z.degree() != 0:
            z -= self.Div([(z.degree(), Infinity)])
        return self.G.find_equivalent_divisor(z)

    def log_series_part(self, z, prec=None):
        r'''
        The sum of the log F_i evaluated at the divisor z (already in the
        fundamental domain).
        '''
        return sum(F.evaluate(z, prec) for FF in self.Fnlist for F in FF.values())

    def __call__(self, z, **kwargs):
        return self.evaluate(z, **kwargs)

    def evaluate(self, z, **kwargs):
        r'''
        Value of theta at z. The rational part is computed exactly, and the
        rest as the exponential of a sum of logarithms.
        '''
        z = self._prepare_divisor(z)
        prec = kwargs.get('prec', None)
        ans0 = pair_divisors(self.val, z)
        return ans0 * exp_small(self.log_series_part(z, prec))

    def eval_derivative(self, z, return_value=False):
        r'''
        Same as ThetaOC.eval_derivative.
        '''
        dlog = self.eval_dlog(z)
        z0 = self.G.to_fundamental_domain(z)[0]
        value = self.evaluate(z0)
        if return_value:
            return value * dlog, value
        else:
            return value * dlog

    def eval_dlog(self, z):
        r'''
        Same as ThetaOC.eval_dlog.
        '''
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
        valdlog = eval_rat_dlog(self.val, z0)
        fdlog = sum((f.eval_dlog(z0) for FF in self.Fnlist for f in FF.values()), valdlog)
        return fact * fdlog

    def evaluate_log(self, z, **kwargs):
        r'''
        Return (v, d, L) such that theta(z) = pi^v * teichmuller(d) * exp(L).

        Only the valuation v and the first digit d (an element of the residue
        field) are computed multiplicatively. L is a sum of logarithms.
        '''
        z = self._prepare_divisor(z)
        prec = kwargs.get('prec', None)
        K = self.K
        q = self.q
        v = 0
        d = K.residue_field()(1)
        L = self.log_series_part(z, prec)
        for P, n in self.val:
            if P is Infinity:
                continue
            for Q, m in z:
                if Q is Infinity:
                    continue
                diff = P - Q
                if diff == 0:
                    continue
                vi = diff.valuation()
                w = diff >> vi
                v += m * n * vi
                d *= w.residue()**(m * n)
                L += (m * n) * principal_part_log(w, q)
        return v, d, L

    def value_from_log(self, v, d, L):
        r'''
        Inverse of evaluate_log.
        '''
        K = self.K
        return K.uniformizer()**v * K.teichmuller(self._lift_residue(d)) * exp_small(L)

    def _lift_residue(self, d):
        K = self.K
        try:
            return K(d)
        except (TypeError, ValueError, NotImplementedError):
            pass
        # Lift through the unramified subfield
        F = K.base_ring()
        return K(F(d))
