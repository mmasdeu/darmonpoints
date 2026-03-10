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

    def __hash__(self):
        try:
            return hash(
                (hash(self.parent()), hash(self.quaternion_rep.coefficient_tuple()))
            )
        except (TypeError, ValueError, AttributeError):
            return hash((hash(self.parent()), hash(tuple(self.quaternion_rep.list()))))

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
        if "P" not in self.parent()._grouptype:
            return selfquatrep == rightquatrep
        tmp = selfquatrep / rightquatrep
        try:
            tmp = self.parent().F(tmp)
        except TypeError:
            return False
        if not tmp.is_integral():
            return False
        elif not (1 / tmp).is_integral():
            return False
        else:
            return True

    def __lt__(self, right):
        if "P" not in self.parent()._grouptype:
            return self.quaternion_rep < right.quaternion_rep
        return False

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
        return self.embed(-1).list().__iter__()

    def matrix(self, prec=-1):
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
        return self.parent().abelianization()(self) == 0

