######################
##                  ##
##    ARITHMETIC    ##
##    GROUP         ##
##    ELEMENT       ##
##                  ##
######################

from collections import defaultdict
from itertools import chain, groupby, islice, product, starmap, tee

from sage.algebras.quatalg.all import QuaternionAlgebra
from sage.functions.generalized import sgn
from sage.functions.trig import arctan
from sage.groups.group import AlgebraicGroup
from sage.matrix.constructor import Matrix
from sage.matrix.constructor import Matrix as matrix
from sage.misc.cachefunc import cached_method
from sage.misc.lazy_attribute import lazy_attribute
from sage.misc.timing import walltime
from sage.misc.misc_c import prod
from sage.misc.persist import db
from sage.modules.free_module_element import free_module_element as vector
from sage.modules.free_module import FreeModule_generic
from sage.rings.rational_field import Q as QQ
from sage.rings.real_mpfr import RR
from sage.rings.integer_ring import Z as ZZ
from sage.rings.complex_mpfr import ComplexField
from sage.rings.number_field.number_field import NumberField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.number_field.number_field import QuadraticField
from sage.rings.real_mpfr import RealField
from sage.rings.padics.factory import Qp
from sage.structure.element import MultiplicativeGroupElement
from sage.structure.richcmp import op_EQ, op_NE, richcmp

from .util import *


class ArithGroupElement(MultiplicativeGroupElement):
    def __init__(self, parent, word_rep=None, quaternion_rep=None, check=False):
        r"""
        Initialize.

        INPUT:

        - a list of the form [(g1,a1),(g2,a2),...,(gn,an)] where the gi are indices
          referring to fixed generators, and the ai are integers, or
          an element of the quaternion algebra ``self.parent().quaternion_algebra()``.

        """
        MultiplicativeGroupElement.__init__(self, parent)
        init_data = False
        self.has_word_rep = False
        self.has_quaternion_rep = False
        if word_rep is not None:
            self.word_rep = word_rep
            self.has_word_rep = True
            init_data = True
        if quaternion_rep is not None:
            if check:
                if not parent._is_in_order(quaternion_rep):
                    raise ValueError(
                        "Quaternion (= %s) must be in order" % quaternion_rep
                    )
                if parent.base_field() == QQ:
                    rednrm = (
                        quaternion_rep.reduced_norm()
                        if self.parent().discriminant != 1
                        else quaternion_rep.determinant()
                    )
                    if rednrm != 1:
                        raise ValueError("Quaternion must be of norm 1")
                else:
                    rednrm = quaternion_rep.reduced_norm()
                    if not rednrm.is_integral() or not (1 / rednrm).is_integral():
                        raise ValueError("Quaternion must be of unit norm")
                if self.has_word_rep:
                    self.check_consistency(quaternion_rep, self.word_rep)
            self.quaternion_rep = quaternion_rep
            set_immutable(self.quaternion_rep)
            self.has_quaternion_rep = True
            init_data = True
        if init_data is False:
            raise ValueError("Must pass either quaternion_rep or word_rep")
        # self._reduce_word()

    def size(self):
        return len(self.word_rep)

    def _is_projective(self):
        r"""
        Whether the ambient group is a projective one, in which case elements
        are only well defined up to scalars.
        """
        return "P" in (self.parent()._grouptype or "")

    def __hash__(self):
        try:
            coeffs = tuple(self.quaternion_rep.coefficient_tuple())
        except (TypeError, ValueError, AttributeError):
            coeffs = tuple(self.quaternion_rep.list())
        if self._is_projective():
            # Elements are only defined up to scalars, so hash a normalized
            # representative. This is coarser than equality (which is up to
            # units), but a coarser hash is still consistent with it.
            for c in coeffs:
                if c != 0:
                    coeffs = tuple(o / c for o in coeffs)
                    break
        return hash((hash(self.parent()), hash(coeffs)))

    def _repr_(self):
        return str(self.quaternion_rep)

    def is_scalar(self):
        try:
            self.parent().base_field()(self.quaternion_rep)
            return True
        except TypeError:
            return False

    def _mul_(left, right):
        word_rep = None
        quaternion_rep = None
        if (left.has_quaternion_rep and right.has_quaternion_rep) or word_rep is None:
            quaternion_rep = left.quaternion_rep * right.quaternion_rep
        return left.__class__(
            left.parent(), word_rep=word_rep, quaternion_rep=quaternion_rep, check=False
        )

    def is_one(self):
        return self.quaternion_rep == 1

    def __invert__(self):
        word_rep = None
        quaternion_rep = None
        if self.has_word_rep:
            word_rep = [-i for i in reversed(self.word_rep)]
        if self.has_quaternion_rep:
            quaternion_rep = self.quaternion_rep ** (-1)
        return self.__class__(
            self.parent(), word_rep=word_rep, quaternion_rep=quaternion_rep, check=False
        )

    def _eq_(self, right):
        selfquatrep = self.quaternion_rep
        rightquatrep = right.quaternion_rep
        if not self._is_projective():
            return selfquatrep == rightquatrep
        # In a projective group the two elements are equal as soon as they
        # differ by a unit scalar.
        tmp = self._scalar_part(selfquatrep / rightquatrep)
        if tmp is None:
            return False
        if not tmp.is_integral():
            return False
        elif not (1 / tmp).is_integral():
            return False
        else:
            return True

    def _scalar_part(self, x):
        r"""
        Return ``x`` as an element of the base field if it is a scalar, and
        ``None`` otherwise. ``x`` may be a quaternion or, when the group is
        given by matrices, a matrix.
        """
        F = self.parent().F
        try:
            return F(x)
        except (TypeError, ValueError):
            pass
        try:
            if not x.is_scalar():
                return None
            return F(x[0, 0])
        except (AttributeError, TypeError, ValueError):
            return None

    def _richcmp_(self, right, op):
        r"""
        Compare two elements.

        Sage routes ``==``, ``<``, ... through ``_richcmp_``, so the comparison
        logic has to live here: a method named ``_eq_`` alone is never called,
        which would silently leave equality comparing by identity.

        TESTS::

            sage: from darmonpoints.sarithgroup import BigArithGroup
            sage: GS = BigArithGroup(5, 6, 1, use_shapiro=False, outfile='/tmp/darmonpoints.tmp') #  optional - magma
            sage: G = GS.small_group() #  optional - magma
            sage: g = G.gen(0) #  optional - magma
            sage: g * g**-1 == G(1) #  optional - magma
            True
            sage: hash(g * g**-1) == hash(G(1)) #  optional - magma
            True
        """
        if op == op_EQ:
            return self._eq_(right)
        if op == op_NE:
            return not self._eq_(right)
        if self._is_projective():
            # No meaningful order on a projective group; report the elements as
            # incomparable rather than imposing a bogus one.
            return False
        return richcmp(self.quaternion_rep, right.quaternion_rep, op)

    def _reduce_word(self):
        if not self.has_word_rep:
            return
        self.word_rep = reduce_word_tietze(self.word_rep)

    @lazy_attribute
    def word_rep(self):
        r"""
        Returns a word in the generators of `\Gamma` representing the given quaternion `x`.
        """
        tmp = self.parent().get_word_rep(self.quaternion_rep)
        self.has_word_rep = True
        return tmp

    @lazy_attribute
    def quaternion_rep(self):
        r"""
        Returns the quaternion representation.
        """
        Gamma = self.parent()
        self.has_quaternion_rep = True
        self.quaternion_rep = prod(
            [Gamma.Ugens[g] ** a for g, a in tietze_to_syllables(self.word_rep)],
            z=Gamma.B.one(),
        )
        set_immutable(self.quaternion_rep)
        return self.quaternion_rep

    def check_consistency(self, q=None, wd=None, txt=""):
        if q is None and wd is None:
            if not self.has_quaternion_rep or not self.has_word_rep:
                return
        if q is None:
            q = self.quaternion_rep
        if wd is None:
            wd = self.word_rep
        Gamma = self.parent()
        F = Gamma.base_field()
        try:
            q1 = prod(
                [Gamma.Ugens[g] ** a for g, a in tietze_to_syllables(wd)], z=ZZ(1)
            )
            quo = F(q * q1**-1)
        except (TypeError, IndexError):
            print("Inconsistency: %s" % (q * q1**-1))
            raise RuntimeError("Word and quaternion are inconsistent! (%s)" % txt)
        return

    @cached_method
    def embed(self, prec):
        assert self.has_quaternion_rep
        return self.parent().embed(self.quaternion_rep, prec)

    def __iter__(self):
        return self.matrix().list().__iter__()

    def matrix(self, prec=-1):
        r"""
        The image of ``self`` under the p-adic embedding, with precision ``prec``.

        The default ``prec = -1`` means the current precision of the embedding
        of the group. It is resolved here, before calling the cached method
        ``embed``: otherwise ``embed(-1)`` would cache the matrix computed at the
        precision of the first call, and keep returning it after the precision
        of the embedding has been raised (in the overconvergent lift, this capped
        the moments at the 200 digits that BigArithGroup starts with).
        """
        if prec == -1:
            try:
                prec = self.parent().embedding_precision()
            except AttributeError:  # groups not attached to a BigArithGroup
                pass
        return self.embed(prec)

    def _act_on_(self, x, on_left):
        assert on_left == True
        if hasattr(x, 'imag'): # x is a complex number
            mat = self.parent().get_archimedean_embedding(x.parent().precision())(self.quaternion_rep)
        else:
            mat = self.matrix()
        try:
            is_field = x.parent().is_field()
        except AttributeError:
            is_field = False
        if is_field:
            a, b, c, d = mat.list()
            if is_infinity(x):
                if c == 0:
                    return x
                else:
                    return a / c
            else:
                return (a * x + b) / (c * x + d)
        else:
            try:
                return mat * x
            except TypeError:
                return x._acted_upon_(self, on_left)

    def conjugate_by(self, w):
        word_rep = None
        quat_rep = None
        if self.has_word_rep:
            if len(self.word_rep) == 0:
                return self
            elif len(self.word_rep) == 1:
                i = self.word_rep[0]
                if i > 0:
                    return self.parent()(
                        w**-1 * self.parent().gen(i - 1).quaternion_rep * w
                    )
                else:
                    return (
                        self.parent()(
                            w**-1 * self.parent().gen(-i - 1).quaternion_rep * w
                        )
                        ** -1
                    )
            else:
                word_rep = []
                for i in self.word_rep:
                    if i > 0:
                        word_rep += self.parent().gen(i - 1).conjugate_by(w).word_rep
                    else:
                        word_rep += (
                            (self.parent().gen(-i - 1) ** -1).conjugate_by(w).word_rep
                        )
        if self.has_quaternion_rep:
            quat_rep = w**-1 * self.quaternion_rep * w
        return self.parent().element_class(
            self.parent(), word_rep=word_rep, quaternion_rep=quat_rep, check=False
        )

    def is_trivial_in_abelianization(self):
        return vector(self.parent().abelianization()(self)) == 0
