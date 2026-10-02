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
'''
from copy import copy

from sage.matrix.constructor import Matrix
from sage.misc.cachefunc import cached_function
from sage.functions.log import log
from sage.misc.verbose import verbose
from sage.modules.free_module_element import free_module_element as vector
from sage.rings.infinity import Infinity
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.structure.sage_object import SageObject

from .divisors import Divisors, DivisorsElement
from .meromorphic import MeromorphicFunctions, evalpoly
from .theta import pair_divisors


@cached_function
def _inverse_integers(K, n):
    r'''
    The list [1/1, 1/2, ..., 1/n] of elements of K.
    '''
    return [None] + [K(QQ(1) / k) for k in range(1, n + 1)]


def _ramification_data(K):
    p = K.prime()
    try:
        e = K.absolute_e()
    except AttributeError:
        e = K.ramification_index()
    return p, ZZ(e)


def log_principal(u, prec=None):
    r'''
    Logarithm of a principal unit u (that is, u = 1 mod the maximal ideal),
    computed with the power series of log(1 + y).

    This is much faster than u.log() for extensions of extensions.
    '''
    K = u.parent()
    p, e = _ramification_data(K)
    y = u - 1
    if y.is_zero():
        return K(0).add_bigoh(u.precision_absolute())
    vy = y.valuation()
    if vy <= 0:
        raise ValueError('Not a principal unit')
    if prec is None:
        prec = u.precision_absolute()
    # The k-th term has valuation k * vy - e * v_p(k) >= f(k) = k * vy - e * log_p(k),
    # and f is increasing for k >= e / (vy * ln(p)). Stop when all the
    # remaining terms are negligible.
    lnp = float(log(p))
    kmax = 1
    while kmax * vy * lnp < e or (kmax + 1) * vy - e * float(log(kmax + 1)) / lnp < prec:
        kmax += 1
    inv = _inverse_integers(K, kmax)
    # Horner: log(1+y) = y (1 - y (1/2 - y (1/3 - ...)))
    ans = inv[kmax]
    for k in range(kmax - 1, 0, -1):
        ans = inv[k] - y * ans
    return (y * ans).add_bigoh(prec)


def exp_small(s, prec=None):
    r'''
    Exponential of s, which is assumed to have valuation > e / (p - 1).
    '''
    K = s.parent()
    p, e = _ramification_data(K)
    if prec is None:
        prec = min(s.precision_absolute(), K.precision_cap())
    if s.is_zero():
        return K(1).add_bigoh(prec)
    vs = s.valuation()
    if vs * (p - 1) <= e:
        raise ValueError('exp does not converge')
    # The k-th term has valuation k * vs - e * v_p(k!) >= k * vs - e * (k - 1) / (p - 1),
    # which is increasing in k. Stop when all the remaining terms are negligible.
    kmax = 1
    while (kmax + 1) * vs - e * QQ(kmax) / (p - 1) < prec:
        kmax += 1
    inv = _inverse_integers(K, kmax)
    # Horner: exp(s) = 1 + s (1 + s/2 (1 + s/3 (...)))
    ans = K(1)
    for k in range(kmax, 0, -1):
        ans = 1 + s * inv[k] * ans
    return ans.add_bigoh(prec)


def principal_part_log(w, q):
    r'''
    For a unit w, return log of its principal part w / teichmuller(w), computed
    as log(w^(q-1)) / (q-1), which avoids computing the Teichmuller lift.
    '''
    return log_principal(w**(q - 1)) / (q - 1)


class LogSeries(SageObject):
    r'''
    Power series log F(t), where t is the coordinate given by the parameter.
    '''
    def __init__(self, value, parameter):
        self._value = value
        self._parameter = parameter

    def evaluate(self, D, prec=None):
        a, b, c, d = self._parameter.list()
        phi = lambda Q: a / c if Q == Infinity else (a * Q + b) / (c * Q + d)
        if isinstance(D, DivisorsElement):
            return sum(n * evalpoly(self._value, phi(P), prec=prec) for P, n in D)
        else:
            return evalpoly(self._value, phi(D), prec=prec)

    def act(self, action_data):
        r'''
        Log of the result of fast_act on the corresponding multiplicative
        series: compose with the Mobius transformation, and normalize so that
        the value at 0 is 0 (the multiplicative version divides by the value at
        0 instead).
        '''
        M, param = action_data
        ans = self._value * M
        ans[0] = 0
        return LogSeries(ans, param)

    def _repr_(self):
        return f'log-series {self._value}'


def log_series_of_divisor(D, parameter, prec):
    r'''
    log of the power series that MeromorphicFunctions(K, p, prec)(D, parameter)
    represents, namely the sum over (Q, n) in D of n * log(1 - x_Q t), where
    x_Q = (c Q + d) / (a Q + b).
    '''
    K = parameter.base_ring()
    a, b, c, d = parameter.list()
    coeffs = [K(0) for _ in range(prec)]
    for Q, n in D:
        x = c / a if Q == Infinity else (c * Q + d) / (a * Q + b)
        if x.valuation() <= 0:
            raise NotImplementedError('The series is not a principal unit')
        xk = x
        for k in range(1, prec):
            coeffs[k] += n * xk
            xk *= x
    inv = _inverse_integers(K, prec)
    coeffs = [K(0)] + [-inv[k] * coeffs[k] for k in range(1, prec)]
    return vector(K, [o.add_bigoh(prec) for o in coeffs])


class ThetaOCAdditive(SageObject):
    r'''
    Additive version of ThetaOC (see the module documentation).

    The interface is the same as that of ThetaOC (including initial_F, which
    is here a dictionary of lists of coefficients of log F_i, and improve with
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

    def _to_vector(self, data):
        K = self.K
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

    def improve(self, m, **kwargs):
        r'''
        Same as ThetaOC.improve.
        '''
        gens_ext = self.G.gens_extended()
        implementation = kwargs.get('implementation', 'list')
        tol = kwargs.get('tol', None)
        if implementation not in ['list', 'fixedpoint']:
            raise ValueError("implementation must be 'list' or 'fixedpoint'")
        action_data = self._get_action_data()
        prec = self.prec
        self.last_change = None
        best = None
        stalled = 0
        for _ in range(m):
            tmp = {}
            for i, _ in gens_ext:
                vl = sum(Fj._value * action_data[i, j][0]
                         for j, Fj in self.Fnlist[-1].items() if i != -j)
                vl[0] = 0
                tmp[i] = vector(self.K, [o.add_bigoh(prec) for o in vl])
            if implementation == 'list':
                new = {i : LogSeries(v, self.F2[i]._parameter) for i, v in tmp.items()}
                self.Fnlist.append(new)
                if tol is not None:
                    change = min(min(o.valuation() for o in v) for v in tmp.values())
            else:
                new = {i : LogSeries(tmp[i] + self.F2[i]._value, self.F2[i]._parameter) for i in tmp}
                if tol is not None:
                    old = self.Fnlist[-1]
                    change = min(min(o.valuation() for o in (new[i]._value - old[i]._value)) for i in new)
                self.Fnlist = [new]
            if tol is not None:
                if best is None or change > best:
                    best = change
                    stalled = 0
                else:
                    stalled += 1
                self.last_change = change
                if change >= tol or stalled >= 2:
                    break
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
