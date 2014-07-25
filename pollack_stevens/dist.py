# cython: profile=True

#*****************************************************************************
#       Copyright (C) 2012 Robert Pollack <rpollack@math.bu.edu>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.structure.sage_object import SageObject
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.rings.polynomial.all import PolynomialRing
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.finite_rings.integer_mod_ring import Zmod
from sage.rings.arith import binomial, bernoulli
from sage.modules.free_module_element import vector, zero_vector
from sage.structure.element import ModuleElement
from sage.matrix.matrix import Matrix
from sage.matrix.matrix_space import MatrixSpace
from sage.matrix.all import matrix
from sage.misc.prandom import random
from sage.functions.other import floor
from sage.structure.element import RingElement, Element
from sage.structure.parent import Parent
import operator
from sage.rings.padics.padic_generic import pAdicGeneric
from sage.rings.padics.padic_capped_absolute_element import pAdicCappedAbsoluteElement
from sage.rings.padics.padic_capped_relative_element import pAdicCappedRelativeElement
from sage.rings.padics.padic_fixed_mod_element import pAdicFixedModElement
from sage.rings.integer import Integer
from sage.rings.rational import Rational
from sage.misc.misc import verbose, cputime
from sage.rings.infinity import Infinity
from sage.categories.action import Action


from sigma0 import Sigma0


def get_dist_classes(p, prec_cap, base, symk):
    r"""
    Determines the element and action classes to be used for given inputs.

    INPUT:

    - ``p``        -- prime

    - ``prec_cap`` -- The p-adic precision cap

    - ``base``     -- The base ring

    - ``symk``     -- An element of Symk

    OUTPUT:

    - Either a Dist_vector and WeightKAction_vector, or a Dist_vector_long
       and WeightKAction_vector_long

    EXAMPLES::

        sage: from sage.modular.pollack_stevens.dist import get_dist_classes
        sage: pass
    """
        
    return Dist_vector, WeightKAction_vector

class Dist(ModuleElement):
    r"""
        The main p-adic distribution class, implemented as per the paper
        'Overconvergent Modular Symbols and p-adic L-functions' by Pollack
        & Stevens
    """
    def moment(self, n):
        r"""
        Returns the `n`-th moment.

        INPUT:

        - ``n`` -- an integer or slice, to be passed on to moments.

        OUTPUT:

        - the `n`-th moment, or a list of moments in the case that `n`
          is a slice.

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions, Symk
        """
        if self.ordp == 0:
            return self._unscaled_moment(n)
        else:
            return self.parent().prime()**(self.ordp) * self._unscaled_moment(n)

    def normalize(self):
        r"""
        Normalize so that the precision of the `i`-th moment is `n-i`,
        where `n` is the number of moments.

        OUTPUT:

        - Normalized entries of the distribution

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions
            sage: D = Distributions(5, 7, 15)
            sage: D
            Space of 7-adic distributions with k=5 action and precision cap 15
            sage: v = D([1,2,3,4,5]); v
            (1 + O(7^5), 2 + O(7^4), 3 + O(7^3), 4 + O(7^2), 5 + O(7))
            sage: v.normalize()
            (1 + O(7^5), 2 + O(7^4), 3 + O(7^3), 4 + O(7^2), 5 + O(7))
        """
        raise NotImplementedError

    def _relprec(self):
        raise NotImplementedError

    def _unscaled_moment(self, i):
        raise NotImplementedError

    def scale(self,left):
        r"""
        Scales the moments of the distribution by `left`

        INPUT:

        - ``left`` -- scalar

        OUTPUT:

        - Scales the moments by `left`

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions
            sage: D = Distributions(5, 7, 15)
            sage: v = D([1,2,3,4,5]); v
            (1 + O(7^5), 2 + O(7^4), 3 + O(7^3), 4 + O(7^2), 5 + O(7))
            sage: v.scale(2)
            (2 + O(7^5), 4 + O(7^4), 6 + O(7^3), 1 + 7 + O(7^2), 3 + O(7))
        """
        R = left.parent()
        base = self.parent().base_ring()
        if base is R:
            return self._lmul_(left)
        elif base.has_coerce_map_from(R):
            return self._lmul_(base(left))
        else:
            from sage.categories.pushout import pushout
            new_base = pushout(base, R)
            V = self.parent().change_ring(new_base)
            scalar = new_base(left)
            return V([scalar * new_base(self.moment(i)) for i in range(self.precision_absolute())])

    def is_zero(self, p=None, M=None):
        r"""
        Returns True if the `i`th moment is zero for all `i` (case M is None)
        or zero modulo p^(M-i) for all `i` (M is not None).

        Note that some moments are not known to precision M, in which
        case they are only checked to be equal to zero modulo the
        precision to which they are defined.

        INPUT:

        - ``p`` -- prime

        - ``M`` -- precision

        OUTPUT:

        - True/False

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions
            sage: D = Distributions(5, 7, 15)
            sage: v = D([1,2,3,4,5]); v
            (1 + O(7^5), 2 + O(7^4), 3 + O(7^3), 4 + O(7^2), 5 + O(7))
            sage: v.is_zero()
            False
            sage: v = D(5*[0])
            sage: v.is_zero()
            True
        """
        n = self.precision_relative()
        aprec = self.precision_absolute()
        if M is None:
            M = n
        elif M > aprec:
            return False
        elif M < aprec:
            n -= (aprec - M)
            M -= self.ordp
        if p is None:
            p = self.parent().prime()
        usearg = True
        if n == 0:
            return True
        else:
            try:
                z = self.moment(0).is_zero(M)
            except TypeError:
                z = self.moment(0).is_zero()
                use_arg = False
            if not z: return False
            for a in xrange(1, n):
                if usearg:
                    z = self._unscaled_moment(a).is_zero(M-a)
                else:
                    z = self._unscaled_moment(a).is_zero()
                if not z: return False
            return True

    def find_scalar(self, _other, p, M = None, check=True):
        r"""
        Returns an ``alpha`` with ``other = self * alpha``, or raises a ValueError.

        It will also raise a ValueError if this distribution is zero.

        INPUT:

        - ``other`` -- another distribution

        - ``p`` -- an integral prime (only used if the parent is not a Symk)

        - ``M`` -- (default: None) an integer, the relative precision
          to which the scalar must be determined

        - ``check`` -- (default: True) boolean, whether to validate
          that ``other`` is actually a multiple of this element.

        OUTPUT:

        - A scalar ``alpha`` with ``other = self * alpha``.

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions
            sage: D = Distributions(5, 7, 15)
            sage: v = D([1,2,3,4,5])
            sage: w = D([3,6,9,12,15])
            sage: v.find_scalar(w,p=7)
            3 + O(7^5)

            sage: u = D([1,4,9,16,25])
            sage: v.find_scalar(u,p=7)
            Traceback (most recent call last):
            ...
            ValueError: not a scalar multiple

        """
        other = _other
        i = 0
        n = self.precision_relative()
        other_pr = other.precision_relative()
        if n == 0:
            raise ValueError("self is zero")
## RP: This code doesn't seem right.  For instance, if the eigenvalue has positive valuation
##     then the relative precision will go down.
##        if n != other.precision_relative():
##            raise ValueError("other should have the same number of moments")
        verbose("n = %s"%n)
        verbose("moment 0")
        a = self._unscaled_moment(i)
        verbose("a = %s"%(a))
        padic = isinstance(a.parent(), pAdicGeneric)
        if self.parent().is_symk():
            while a == 0:
                if other._unscaled_moment(i) != 0:
                    raise ValueError("not a scalar multiple")
                i += 1
                verbose("moment %s"%i)
                try:
                    a = self._unscaled_moment(i)
                except IndexError:
                    raise ValueError("self is zero")
            alpha = other._unscaled_moment(i) / a
            if check:
                i += 1
                while i < n:
                    verbose("comparing moment %s"%i)
                    if alpha * self._unscaled_moment(i) != other._unscaled_moment(i):
                        raise ValueError("not a scalar multiple")
                    i += 1
        else:
            p = self.parent().prime()
            v = a.valuation(p)
            while v >= n - i:
                i += 1
                verbose("p moment %s"%i)
                try:
                    a = self._unscaled_moment(i)
                except IndexError:
                    raise ValueError("self is zero")
                v = a.valuation(p)
            relprec = n - i - v
#            verbose("p=%s, n-i=%s\nself.moment=%s, other.moment=%s"%(p, n-i, a, other._unscaled_moment(i)),level=2)
## RP: This code was crashing because other may have too few moments -- so I added this bound with other's relative precision
            if padic:
                if i < other_pr:
                    alpha = (other._unscaled_moment(i) / a).add_bigoh(n-i)
                else:
                    alpha = (0*a).add_bigoh(other_pr-i)
            else:
                if i < other_pr:
                    alpha = (other._unscaled_moment(i) / a) % p**(n-i)
                else:
                    alpha = 0
            verbose("alpha = %s"%(alpha))
## RP: This code was crashing because other may have too few moments -- so I added this bound with other's relative precision
            while i < other_pr-1:
                i += 1
                verbose("comparing p moment %s"%i)
                a = self._unscaled_moment(i)
                if check:
#                    verbose("self.moment=%s, other.moment=%s"%(a, other._unscaled_moment(i)))
                    if (padic and other._unscaled_moment(i) != alpha * a) or \
                       (not padic and other._unscaled_moment(i) % p**(n-i) != alpha * a % p**(n-i)):
                        raise ValueError("not a scalar multiple")
                v = a.valuation(p)
                if n - i - v > relprec:
                    verbose("Reseting alpha: relprec=%s, n-i=%s, v=%s"%(relprec, n-i, v))
                    relprec = n - i - v
                    if padic:
                        alpha = (other._unscaled_moment(i) / a).add_bigoh(n-i)
                    else:
                        alpha = (other._unscaled_moment(i) / a) % p**(n-i)
                    verbose("alpha=%s"%(alpha))
            if relprec < M:
                raise ValueError("result not determined to high enough precision")
        alpha = alpha * self.parent().prime()**(other.ordp - self.ordp)
        verbose("alpha=%s"%(alpha))
        try:
            return self.parent().base_ring()(alpha)
        except ValueError:
            return alpha

    def _rmul_(self, _left):
        """
        Scalar multiplication.

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions
        """
        return self._lmul_(_left)

    def __cmp__(_left, _right):
        r"""
        Comparison.

        EXAMPLES:

        Equality of two :class:`Dist_vector`::

            # XXX FIXME

        """
        left = _left
        right = _right
        left.normalize()
        right.normalize()
        rprec = min(left._relprec(), right._relprec())
        p = left.parent().prime()
        if left.ordp > right.ordp:
            shift = p ** (left.ordp - right.ordp)
            for i in range(rprec):
                c = cmp(shift * left._unscaled_moment(i), right._unscaled_moment(i))
                if c: return c
        elif left.ordp < right.ordp:
            shift = p ** (right.ordp - left.ordp)
            for i in range(rprec):
                c = cmp(left._unscaled_moment(i), shift * right._unscaled_moment(i))
                if c: return c
        else:
            for i in range(rprec):
                c = cmp(left._unscaled_moment(i), right._unscaled_moment(i))
                if c: return c
        return 0

    def diagonal_valuation(self, p=None):
        """
        Returns the largest `m` so that this distribution lies in `Fil^m`.

        INPUT:

        - ``p`` -- (default: None) a positive integral prime

        OUTPUT:

        - the largest integer `m` so that `p^m` divides the `0`-th
          moment, `p^{m-1}` divides the first moment, etc.

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions
            sage: D = Distributions(8, 7, 15)
            sage: v = D([7^(5-i) for i in range(1,5)])
            sage: v
            (O(7^4), O(7^3), O(7^2), O(7))
            sage: v.diagonal_valuation(7)
            4
        """
        if p is None:
            p = self.parent()._p
        n = self.precision_relative()
        return self.ordp + min([n] + [a + self._unscaled_moment(a).valuation(p) for a in range(n)])

    def valuation(self, p=None):
        """
        Returns the minimum valuation of any moment.

        INPUT:

        - ``p`` -- (default: None) a positive integral prime

        OUTPUT:

        - 

        .. WARNING::

            Since only finitely many moments are computed, this valuation may
            be larger than the actual valuation of this distribution.
            Moreover, since distributions are normalized so that the top moment
            has precision 1, this valuation may be smaller than the actual
            valuation (for example, if the actual valuation is 2)

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions
            sage: D = Distributions(8, 7, 15)
            sage: v = D([7^(5-i) for i in range(1,5)])
            sage: v
            (O(7^4), O(7^3), O(7^2), O(7))
            sage: v.valuation(7)
            1
        """
        if p is None:
            p = self.parent()._p
        n = self.precision_relative()
        if self.parent().is_symk():
            return self.ordp + min([self._unscaled_moment(a).valuation(p) for a in range(n)])
        else:
            return self.ordp + min([n] + [self._unscaled_moment(a).valuation(p) for a in range(n) if not self._unscaled_moment(a).is_zero()])


    def specialize(self, new_base_ring=None):
        """
        Returns the image of this overconvergent distribution under
        the canonical projection from distributions of weight k to
        Sym^k.

        INPUT:

        - ``new_base_ring`` -- (default: None) a ring giving the
          desired base ring of the result.

        OUTPUT:

        - An element of Sym^k(K), where K is the specified base ring.

        EXAMPLES::

            sage: D = Distributions(4, 13)
            sage: d = D([0,2,4,6,8,10,12])
            sage: d.specialize()          
            (O(13^7), 2 + O(13^6), 4 + O(13^5), 6 + O(13^4), 8 + O(13^3))

        """
        self.normalize()
        k=self.parent()._k
        if k < 0:
            raise ValueError("negative weight")
        if self.precision_absolute() < k+1:
            raise ValueError("not enough moments")
        V = self.parent().specialize(new_base_ring)
        new_base_ring = V.base_ring()
        if self.precision_relative() == 0:
            return V.zero_element()
        else:
            return V([new_base_ring.coerce(self.moment(j)) for j in range(k+1)])

    def lift(self, p=None, M=None, new_base_ring=None):
        r"""
        Lifts a distribution or element of Sym^k to an overconvergent distribution.

        INPUT:

        - ``p`` -- (default: None) a positive integral prime.  If None
          then p must be available in the parent.

        - ``M`` -- (default: None) a positive integer giving the
          desired number of moments. If None, returns a distribution having one
          more moment than this one.

        - ``new_base_ring`` -- (default: None) a ring giving the desired base
          ring of the result. If None, a base ring is chosen automatically.

        OUTPUT:

        - An overconvergent distribution with `M` moments whose image
          under the specialization map is this element.

        EXAMPLES::

            sage: V = Symk(0)      
            sage: x = V(1/4)       
            sage: y = x.lift(17, 5)
            sage: y                
            (13 + 12*17 + 12*17^2 + 12*17^3 + 12*17^4 + O(17^5), O(17^4), O(17^3), O(17^2), O(17))
            sage: y.specialize()._moments == x._moments 
            True
        """
        V = self.parent().lift(p, M, new_base_ring)
        k = V._k
        p = V.prime()
        M = V.precision_cap()
        R = V.base_ring()
        moments = [R.coerce(self.moment(j)) for j in range(k+1)]
        zero = R(0)
        moments.extend([zero] * (M - k - 1))
        mu = V(moments)
        #val = mu.valuation()
        #if val < 0:
        #    # This seems unnatural
        #    print "scaling by %s^%s to keep things integral"%(p, -val)
        #    mu *= p**(-val)
        return mu

    def _is_malformed(self):
        r"""
        Check that the precision of self is sensible.

        EXAMPLE::

            sage: D = sage.modular.pollack_stevens.distributions.Symk(2, base=Qp(5))
            sage: v = D([1, 2, 3])
            sage: v._is_malformed()
            False
            sage: v = D([1 + O(5), 2, 3])
            sage: v._is_malformed()
            True
        """
        n = self.precision_absolute()
        for i in range(n):
            if self.moment(i).precision_absolute() < n - i:
                return True
        return False

    def act_right(self,gamma):
        r"""
        The image of this element under the right action by a
        `2 \times 2` matrix.

        INPUT:

        - ``gamma`` -- the matrix by which to act

        OUTPUT:

        - ``self | gamma``

        .. NOTE::

            You may also just use multiplication ``self * gamma``.

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions
        """
        return self.parent()._act(self, gamma)

class Dist_vector(Dist):
    r"""
    A distribution is stored as a vector whose `j`-th entry is the `j`-th moment of the distribution.

    The `j`-th entry is stored modulo `p^(N-j)` where `N` is the total number of moments.
    (This is the accuracy that is maintained after acting by `\Gamma_0(p)`.)

    INPUTS:

    - ``moments`` -- the list of moments.  If ``check == False`` it
      must be a vector in the appropriate approximation module.

    - ``parent`` -- a :class:`distributions.Distributions_class` or
      :class:`distributions.Symk_class` instance

    - ``ordp`` -- an integer.  This MUST be zero in the case of Symk
      of an exact ring.

    - ``check`` -- (default: True) boolean, whether to validate input

    EXAMPLES::

        sage: from sage.modular.pollack_stevens.distributions import Distributions
    """
    def __init__(self, parent, moments = None, ordp=0, check=True):
        """
        Initialization.

        TESTS::

            sage: from sage.modular.pollack_stevens.distributions import Symk
            sage: Symk(4)(0)
            (0, 0, 0, 0, 0)
            
        """
        if not isinstance(parent,Parent):
            parent,moments = moments,parent

        Dist.__init__(self, parent)
        if moments is None:
            return
        if check:
            # case 1: input is a distribution already
            if isinstance(moments, Dist):
                moments = moments._moments.change_ring(parent.base_ring())
            # case 2: input is a vector, or something with a len
            elif hasattr(moments, '__len__'):
                M = len(moments)
                moments = parent.approx_module(M)(moments)
            # case 3: input is zero
            elif moments == 0:
                moments = parent.approx_module(parent.precision_cap())(moments)
            # case 4: everything else
            else:
                moments = parent.approx_module(1)([moments])
            # TODO: This is not quite right if the input is an inexact zero.
            if ordp != 0 and parent.prime() == 0:
                raise ValueError("can not specify a valuation shift for an exact ring")

        ## RP: if the input has negative valuations everything was crashing so I added
        ##     this code, but I don't feel good about it.  DOESN'T WORK!!!!
#        if self.parent().prime() != 0:
#            p = self.parent().prime()
#            ordp = min([m.valuation(p) for m in moments])
#            moments = [p**(-ordp) * moments[a] for a in range(len(moments))]

        self._moments = moments
        self.ordp = ordp

    def __reduce__(self):
        r"""
        Used for pickling.

        EXAMPLE::

            sage: D = sage.modular.pollack_stevens.distributions.Symk(2)
            sage: x = D([2,3,4])
            sage: x.__reduce__()
            (<type 'sage.modular.pollack_stevens.dist.Dist_vector'>, ((2, 3, 4), Sym^2 Q^2, False))
        """
        return (self.__class__,(self._moments,self.parent(),False))

    def _new_c(self):
        r"""
        Creates an empty distribution.

        Note that you MUST fill in the ordp attribute on the resulting distribution.

        OUTPUT:

        - A distribution with no moments.  The moments are then filled
          in by the calling function.

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions
        """
        ans = Dist_vector(self.parent())
        return ans

    def _repr_(self):
        r"""
        String representation.

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions
        """
        r"""
        Displays the moments of the distribution
        """
        self.normalize()
        valstr = ""
        if self.ordp == 1:
            valstr = "%s * "%(self.parent().prime())
        elif self.ordp != 0:
            valstr = "%s^%s * "%(self.parent().prime(), self.ordp)
        if len(self._moments) == 1:
            return valstr + repr(self._moments[0])
        else:
            return valstr + repr(self._moments)

    def _rational_(self):
        """
        Convert to a rational number.

        EXAMPLES::

            sage: D = Symk(0); d = D(4/3); d
            4/3
            sage: QQ(d)
            4/3

        We get a TypeError if there is more than 1 moment::

            sage: D = Symk(1); d = D([1,2]); d
            (1, 2)
            sage: QQ(d)
            Traceback (most recent call last):
            ...
            TypeError: k must be 0
        """
        if len(self._moments) == 1:
            return QQ(self.moment(0))
        raise TypeError, "k must be 0"

    def _relprec(self):
        return len(self._moments)

    def _unscaled_moment(self, n):
        r"""
        Returns the `n`-th moment, unscaled by the overall power of p stored in self.ordp.
        """
        return self._moments[n]
        

    def _addsub(self, right, negate):
        r"""
        Common code for the sum and the difference of two distributions
        """
        ans = self._new_c()
        aprec = min(self.ordp + len(self._moments), right.ordp + len(right._moments))
        ans.ordp = min(self.ordp, right.ordp)
        rprec = aprec - ans.ordp
        # In the case of symk, rprec will always be k
        V = ans.parent().approx_module(rprec)
        R = V.base_ring()
        smoments = self._moments
        rmoments = right._moments
        # we truncate if the moments are too long; extend by zero if too short
        if smoments.parent() is not V:
            #vv = smoments.list(copy=False)
            #print len(vv), len(vv[:rprec]), rprec
            #xx = [R(0)] * (rprec - len(smoments)) if rprec > len(smoments) else []
            #print len(xx)
            #ww = vv[:rprec] + xx
            #print len(ww)
            #smoments = V(ww)
            smoments = V(smoments.list(copy=False)[:rprec] + ([R(0)] * (rprec - len(smoments)) if rprec > len(smoments) else []))
        if rmoments.parent() is not V:
            #vv = rmoments.list(copy=False)
            #xx = [R(0)] * (rprec - len(rmoments)) if rprec > len(rmoments) else []
            #ww = vv[:rprec] + xx
            #rmoments = V(ww)
            rmoments = V(rmoments.list(copy=False)[:rprec] + ([R(0)] * (rprec - len(rmoments)) if rprec > len(rmoments) else []))
        # We multiply by the relative power of p
        if self.ordp > right.ordp:
            smoments *= self.parent().prime()**(self.ordp - right.ordp)
        elif self.ordp < right.ordp:
            rmoments *= self.parent().prime()**(right.ordp - self.ordp)
        if negate:
            rmoments = -rmoments
        ans._moments = smoments + rmoments
        return ans

    def _add_(self, _right):
        r"""
        Sum of two distributions.

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions, Symk
        """
        return self._addsub(_right, False)

    def _sub_(self, _right):
        r"""
        Difference of two distributions.

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions, Symk
        """
        return self._addsub(_right, True)

    def _lmul_(self, right):
        r"""
        Scalar product of a distribution with a ring element that coerces into the base ring.

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions, Symk
        """
        ans = self._new_c()
        p = self.parent().prime()
        if p == 0:
            ans._moments = self._moments * right
            ans.ordp = self.ordp
        elif right.valuation(p) == Infinity:
            ans._moments = self.parent().approx_module(0)([])
            ans.ordp += self.precision_relative()
## RP: I don't understand this is_exact_zero command
## This changes makes the function work when scaling by 0 -- it might
## cause other problems...
#        elif right.is_zero():
#            ans._moments = self.parent().approx_module(0)([])
#            if right.is_exact_zero():
#                ans.ordp = maxordp
#            else:
#                ans.ordp = self.ordp + right.valuation(p)
        else:
            #print right, right.parent()
            try:
                v, u = right.val_unit(p)
            except TypeError: # bug in p-adics: they should accept p here
                v, u = right.val_unit()
            ans._moments = self._moments * u
            ans.ordp = self.ordp + v
            # if the relative precision of u is less than that of self, ans may not be normalized.
        return ans

    def precision_relative(self):
        r"""
        The relative precision of this distribution.

        The precision is just the number of moments stored, which is
        also k+1 in the case of Sym^k(R).  For overconvergent
        distributions, the precision is the integer `m` so that the
        sequence of moments is known modulo `Fil^m`.

        OUTPUT:

        - An integer giving the number of moments.
        """
        return Integer(len(self._moments))

    def precision_absolute(self):
        r"""
        Returns the absolute precision of this distribution.

        The absolute precision is the sum of the relative precision
        (number of moments) and the valuation.

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions, Symk
        """
        return Integer(len(self._moments) + self.ordp)

    def normalize(self):
        r"""
        Normalize by reducing modulo `Fil^N`, where `N` is the number of moments.

        If the parent is Symk, then normalize has no effect.  If the
        parent is a space of distributions, then normalize reduces the
        `i`-th moment modulo `p^{N-i}`.

        OUTPUT:

        - this distribtion, after normalizing.

        .. WARNING::

            This function modifies the distribution in place as well as returning it.

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions, Symk
        """
        return self # DEBUG
        if not self.parent().is_symk(): # non-classical
            V = self._moments.parent()
            R = V.base_ring()
            n = self.precision_relative()
            p = self.parent()._p
            if isinstance(R, pAdicGeneric):
                self._moments = V([self._moments[i].add_bigoh(n-i) for i in range(n)])
            else:
                self._moments = V([self._moments[i]%(p**(n-i)) for i in range(n)])
            shift = self.valuation() - self.ordp
            if shift != 0:
                V = self.parent().approx_module(n-shift)
                self.ordp += shift
                self._moments = V([self._moments[i] // p**shift for i in range(n-shift)])
        return self

    def reduce_precision(self, M):
        r"""
        Only hold on to `M` moments.

        INPUT:

        - ``M`` -- a positive integer less than the precision of this
          distribution.

        OUTPUT:

        - a new distribution with `M` moments equal to the first `M`
          moments of this distribution.

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions, Symk
        """
        assert M<=self.precision_relative(),"not enough moments"

        ans = self._new_c()
        ans._moments = self._moments[:M]
        ans.ordp = self.ordp
        return ans

    def solve_diff_eqn(self):
        r"""
        Solves the difference equation.

        See Theorem 4.5 and Lemma 4.4 of [PS].

        OUTPUT:

        - a distribution v so that self = v | Delta, where Delta = [1, 1; 0, 1] - 1.

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions, Symk
        """
        # assert self._moments[0][0]==0, "not total measure zero"
        # print "result accurate modulo p^",self.moment(0).valuation(self.p)
        #v=[0 for j in range(0,i)]+[binomial(j,i)*bernoulli(j-i) for j in range(i,M)]
        M = self.precision_relative()
        R = self.parent().base_ring()
        K = R.fraction_field()
        V = self._moments.parent()
        v = [K(0) for i in range(M)]
        bern = [bernoulli(i) for i in range(0,M,2)]
        minhalf = ~K(-2)
        for m in range(1,M):
            scalar = K(self.moment(m) / m)
            # bernoulli(1) = -1/2; the only nonzero odd bernoulli number
            v[m] += m * minhalf * scalar 
            for j in range(m-1,M,2):
                v[j] += binomial(j,m-1) * bern[(j-m+1)//2] * scalar
        p = self.parent().prime()

        if p == 0:
            if R.is_field():
                ans = self._new_c()
                ans.ordp = 0
                ans._moments = V(v)
            else:
                newparent = self.parent().change_ring(K)
                ans = newparent(v)
        else:
            ans = self._new_c()
            ans.ordp = min(a.valuation(p) for a in v)
            if ans.ordp < 0:
                scalar = K(p) ** (-ans.ordp)
                ans._moments = V([R(a * scalar) for a in v])
            elif ans.ordp > 0:
                scalar = K(p) ** ans.ordp
                ans._moments = V([R(a // scalar) for a in v])
            else:
                ans._moments = V([R(a) for a in v])
            v = ans._moments
            N = len(ans._moments)
            prec_loss = max([N-j-v[j].precision_absolute() for j in range(N)])
            #            print "precision loss = ",prec_loss
            if prec_loss > 0:
                ans._moments = ans._moments[:(N-prec_loss)]
        return ans


class WeightKAction(Action):
    r"""

    INPUT:

    - ``Dk`` -- a space of distributions
    - ``character`` -- data specifying a Dirichlet character to apply to the
      top right corner, and a power of the determinant by which to scale.  See
      the documentation of
      :class:`sage.modular.pollack_stevens.distributions.Distributions_factory`
      for more details.
    - ``adjuster`` -- a callable object that turns matrices into 4-tuples.
    - ``on_left`` -- whether this action should be on the left.
    - ``dettwist`` -- a power of the determinant to twist by
    - ``padic`` -- if True, define an action of p-adic matrices (not just integer ones)

    OUTPUT:

    - 

    EXAMPLES::

        sage: from sage.modular.pollack_stevens.distributions import Distributions, Symk
    """
    def __init__(self, Dk, character, adjuster, on_left, dettwist, padic=False):
        r"""
        Initialization.

        TESTS::

            sage: from sage.modular.pollack_stevens.distributions import Distributions, Symk
        """
        self._k = Dk._k
#        if self._k < 0: raise ValueError("k must not be negative")
        self._adjuster = adjuster
        self._character = character
        self._dettwist = dettwist
        self._p = Dk._p
        self._symk = Dk.is_symk()
        self._actmat = {}
        self._maxprecs = {}
        if character is None:
            self._Np = ZZ(1) # all of M2Z acts
        else:
            self._Np = character.modulus()
        if not self._symk:
            self._Np = self._Np.lcm(self._p)

        if padic:
            self._Sigma0 = Sigma0(self._Np, base_ring=Dk.base_ring(), adjuster=self._adjuster)
        else:
            self._Sigma0 = Sigma0(self._Np, base_ring=ZZ, adjuster=self._adjuster)
        Action.__init__(self, self._Sigma0, Dk, on_left, operator.mul)

    def clear_cache(self):
        r"""
        

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions, Symk
        """
        self._actmat = {}
        self._maxprecs = {}

    def acting_matrix(self, g, M):
        r"""
        

        INPUT:

        - ``g`` -- an instance of
          :class:`sage.matrices.matrix_integer_2x2.Matrix_integer_2x2`
          or of :class:`sage.matrix.matrix_generic_dense.Matrix_generic_dense`

        - ``M`` -- a positive integer giving the precision at which
          ``g`` should act.

        OUTPUT:

        - An `M \times M` matrix so that the action of `g` on a
          distribution with `M` moments is given by a vector-matrix
          multiplication.

        .. NOTE::

            This function caches its results.  To clear the cache use
            :meth:`clear_cache`.

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions, Symk
        """
        g = g.matrix()
        if not self._maxprecs.has_key(g):
            A = self._compute_acting_matrix(g, M)
            self._actmat[g] = {M:A}
            self._maxprecs[g] = M
            return A
        else:
            mats = self._actmat[g]
            if mats.has_key(M):
                return mats[M]
            maxprec = self._maxprecs[g]
            if M < maxprec:
                A = mats[maxprec][:M,:M] # submatrix; might want to reduce precisions
                mats[M] = A
                return A
            if M < 30: # This should not be hard-coded
                maxprec = max([M,2*maxprec]) # This may be wasting memory
            else:
                maxprec = M
            self._maxprecs[g] = maxprec
            mats[maxprec] = self._compute_acting_matrix(g, maxprec) # could lift from current maxprec
            if M == maxprec:
                return mats[maxprec]
            A = mats[maxprec][:M,:M] # submatrix; might want to reduce precisions
            mats[M] = A
            return A


    def _compute_acting_matrix(self, g, M):
        r"""
        

        INPUT:

        - ``g`` -- an instance of
          :class:`sage.matrices.matrix_integer_2x2.Matrix_integer_2x2`

        - ``M`` -- a positive integer giving the precision at which
          ``g`` should act.

        OUTPUT:

        - 

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions, Symk
        """
        """
        Forms a large M x M matrix say G such that if v is the vector of
        moments of a distribution mu, then v*G is the vector of moments of
        mu|[a,b;c,d]
        """
        raise NotImplementedError

class WeightKAction_vector(WeightKAction):
    def _compute_acting_matrix(self, g, M):
        r"""
        

        INPUT:

        - ``g`` -- an instance of
          :class:`sage.matrices.matrix_integer_2x2.Matrix_integer_2x2`
          or :class:`sage.matrix.matrix_generic_dense.Matrix_generic_dense`

        - ``M`` -- a positive integer giving the precision at which
          ``g`` should act.

        OUTPUT:

        - 

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions, Symk
        """
        #tim = verbose("Starting")
        a, b, c, d = self._adjuster(g)
        # if g.parent().base_ring().is_exact():
        #     self._check_mat(a, b, c, d)
        k = self._k
        if g.parent().base_ring() is ZZ:
            if self._symk:
                base_ring = QQ
            else:
                base_ring = Zmod(self._p**M)
        else:
            base_ring = g.parent().base_ring()
        B = matrix(base_ring,M,M)
        if M == 0:
            return B.change_ring(self.codomain().base_ring())
        R = PowerSeriesRing(base_ring, 'y', default_prec = M)
        y = R.gen()
        #tim = verbose("Checked, made R",tim)
        # special case for small precision, large weight
        scale = (b+d*y)/(a+c*y)
        t = (a+c*y)**k # will already have precision M

        #tim = verbose("Made matrix",tim)
        for col in range(M):
            for row in range(M):
                B[row,col] = t[row]
            t *= scale
        #verbose("Finished loop",tim)
        # the changering here is annoying, but otherwise we have to change ring each time we multiply
        B = B.change_ring(self.codomain().base_ring())
        if self._character is not None:
            B *= self._character(a)
        if self._dettwist is not None:
            B *= (a*d - b*c)**(self._dettwist)
        try:
            B = B.apply_map(operator.methodcaller('lift'))
        except AttributeError: pass
        return B

    def _call_(self, _v, g):
        r"""
        

        INPUT:

        - ``_v`` -- a :class:`Dist_vector` instance, the distribution
          on which to act.

        - ``g`` -- a
          :class:`sage.matrix.matrix_integer_2x2.Matrix_integer_2x2`
          instance, the `2 \times 2` matrix that is acting.

        OUTPUT:

        - 

        EXAMPLES::

            sage: from sage.modular.pollack_stevens.distributions import Distributions, Symk
        """
        # if g is a matrix it needs to be immutable
        # hashing on arithmetic_subgroup_elements is by str
        if self.is_left():
            _v,g = g,_v
        if g == 1:
            return _v
        v = _v
        ans = v._new_c()
        #try:
        #    g.set_immutable()
        #except AttributeError:
        #    pass
        try:
            v_moments = v._moments.apply_map(operator.methodcaller('lift'))
        except AttributeError:
            v_moments = v._moments
        ans._moments = v_moments * self.acting_matrix(g, len(v_moments))
        ans.ordp = v.ordp
        return ans
