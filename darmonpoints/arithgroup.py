######################
##                  ##
##    QUATERNIONIC  ##
##    ARITHMETIC    ##
##    GROUP         ##
##                  ##
######################
from sage.structure.sage_object import SageObject
from sage.misc.all import cached_method,walltime
from sage.groups.group import AlgebraicGroup
from sage.structure.element import MultiplicativeGroupElement
from sage.algebras.quatalg.all import QuaternionAlgebra
from sage.matrix.all import matrix,Matrix
from sage.modules.all import vector
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,NumberField,QQ,ZZ,Qp, AA
from sage.arith.all import lcm
from sage.functions.trig import arctan
from sage.misc.misc_c import prod
from collections import defaultdict
from itertools import product,chain,izip,groupby,islice,tee,starmap
from sage.structure.sage_object import save,load
from copy import copy
from sage.misc.persist import db
from sage.modules.free_module import FreeModule_generic
from sage.functions.generalized import sgn
from sage.matrix.matrix_space import MatrixSpace

from sage.misc.sage_eval import sage_eval
from util import *
from sage.modules.fg_pid.fgp_module import FGP_Module
from sage.modular.arithgroup.congroup_sl2z import SL2Z
from sage.geometry.hyperbolic_space.hyperbolic_geodesic import HyperbolicGeodesicUHP
from sage.rings.infinity import Infinity
from arithgroup_generic import ArithGroup_generic
from sage.plot.hyperbolic_polygon import hyperbolic_polygon
from sage.repl.rich_output.pretty_print import show
from sage.plot.plot import plot
from sage.plot.hyperbolic_arc import hyperbolic_arc
from sage.plot.hyperbolic_polygon import hyperbolic_polygon
from sage.geometry.hyperbolic_space.hyperbolic_interface import HyperbolicPlane
from util import update_progress
from sage.groups.free_group import FreeGroup

def geodesic_circle(alpha, beta, return_equation=True):
    r'''
    From a picture (pg 79) in "Hyperbolic Geometry",
    in an article Cannon, Floyd, Kenyon, Parry
    '''
    K = alpha.parent() if not is_infinity(alpha) else beta.parent()

    if is_infinity(alpha):
        alpha, beta = beta, alpha
    if is_infinity(beta) or (alpha.real() - beta.real()).abs() < 10**-10:
        x, y = PolynomialRing(K,2,names='x,y').gens()
        return x - alpha.real() if return_equation is True  else (alpha.real(), Infinity)

    z0 = (alpha + beta) / 2
    z1 = (beta - alpha) * K(-1).sqrt()
    t = -z0.imag() / z1.imag()
    C = (z0 + z1 * t)
    verbose('z0 = %s, z1 = %s, t = %s, C = %s'%(z0, z1, t, C))
    assert C.imag().abs() < 10**-10, C
    try:
        r2 = (alpha - C).norm()
    except AttributError:
        r2 = (alpha - C)**2
    x, y = PolynomialRing(C.parent(),2,names='x,y').gens()
    return  (x - C.real())**2 + y**2 - r2 if return_equation is True else (C.real(), r2)

def is_in_open_interval(x,a,b, eps=10**-10):
    a,b = sorted([a,b])
    if b is Infinity:
        return x-a > eps
    else:
        return x > a + eps and x < b - eps

def perturb_point_on_arc(x1, x2, z, r):
    r = z.real().parent()(r)
    center, r2 = geodesic_circle(x1, x2,False)
    ans = []
    CC = z.parent()
    rnorm = r / (z.imag()**2)
    ans.append(CC(z.real() + rnorm, (r2 - (z.real() + rnorm - center)**2).sqrt()))
    ans.append(CC(z.real() - rnorm, (r2 - (z.real() - rnorm - center)**2).sqrt()))
    return ans

def intersect_geodesic_arcs(x1, x2, y1, y2):
    r'''
    TESTS::

    sage: from darmonpoints.arithgroup import intersect_geodesic_arcs
    sage: intersect_geodesic_arcs(1,3,2,4)
    1/2*I*sqrt(3) + 5/2
    sage: print(intersect_geodesic_arcs(-1, 1, 0, AA(-1).sqrt()))
    None
    sage: intersect_geodesic_arcs(-1, 1, 0, 2*AA(-1).sqrt())
    I
    sage: intersect_geodesic_arcs(-3, 3, 2*AA(-1).sqrt(), Infinity)
    3*I
    '''
    verbose('Entering intersect_geodesic_arcs')
    e1 = geodesic_circle(x1, x2)
    e2 = geodesic_circle(y1, y2)
    if e2.degree() == 1: # e2 is a line
        e1, e2 = e2, e1
        x1, x2, y1, y2 = y1, y2, x1, x2
    if e1.degree() == 1: # e1 is a line
        if e2.degree() == 1: # Both are lines!
            verbose('Done intersect_geodesic_arcs')
            return None
        alpha = -e1.constant_coefficient() # x-coordinate of intersection
        x, y = e2.parent().gens()
        y_squared = -e2.subs({x: alpha}).constant_coefficient() # y-coordinate of intersection, squared
        if y_squared < 0:
            verbose('Done intersect_geodesic_arcs')
            return None
        else:
            yy = y_squared.sqrt()
            if is_in_open_interval(yy, imag_part(x1), imag_part(x2),0) \
               and is_in_open_interval(alpha, real_part(y1), real_part(y2),0):
                verbose('Done intersect_geodesic_arcs')
                return alpha + yy * AA(-1).sqrt()
            else:
                verbose('Done intersect_geodesic_arcs')
                return None
    e = e1 - e2
    x,y = e.parent().gens()
    xx = -e.constant_coefficient() / e.monomial_coefficient(x)
    x,y = e1.parent().gens()
    y_squared = -e1.subs({x: xx}).constant_coefficient()
    if y_squared < 0:
        verbose('Done intersect_geodesic_arcs')
        return None
    if is_in_open_interval(xx, real_part(x1), real_part(x2),0) \
       and is_in_open_interval(xx, real_part(y1), real_part(y2),0):
        yy = y_squared.sqrt()
        verbose('Done intersect_geodesic_arcs')
        return xx + yy * AA(-1).sqrt()
    else:
        verbose('Done intersect_geodesic_arcs')
        return None

def sorted_ideal_endpoints(self):
    r"""
    Determine the ideal (boundary) endpoints of the complete
    hyperbolic geodesic corresponding to ``self``.

    OUTPUT:

    - a list of 2 boundary points

    """

    start = self._start.coordinates()
    end = self._end.coordinates()
    [x1, x2] = [real_part(k) for k in [start, end]]
    [y1, y2] = [imag_part(k) for k in [start, end]]
    M = self._model
    # infinity is the first endpoint, so the other ideal endpoint
    # is just the real part of the second coordinate
    if start == Infinity:
        return [M.get_point(start), M.get_point(x2)]
    # Same idea as above
    if end == Infinity:
        return [M.get_point(x1), M.get_point(end)]
    # We could also have a vertical line with two interior points
    if x1 == x2:
        if y1 < y2:
            return [M.get_point(x1), M.get_point(Infinity)]
        else:
            return [M.get_point(Infinity), M.get_point(x1)]
    # Otherwise, we have a semicircular arc in the UHP
    c = ((x1+x2)*(x2-x1) + (y1+y2)*(y2-y1)) / (2*(x2-x1))
    r = ((c - x1)**2 + y1**2).sqrt()
    if x1 < x2:
        return [M.get_point(c - r), M.get_point(c + r)]
    else:
        return [M.get_point(c + r), M.get_point(c - r)]

def moebius_transform(A, z):
    r"""
    Given a matrix ``A`` in `GL(2, \CC)` and a point ``z`` in the complex
    plane return the Moebius transformation action of ``A`` on ``z``.

    INPUT:

    - ``A`` -- a `2 \times 2` invertible matrix over the complex numbers
    - ``z`` -- a complex number or infinity

    OUTPUT:

    - a complex number or infinity
    """
    if A.ncols() == 2 and A.nrows() == 2 and A.det() != 0:
        (a, b, c, d) = A.list()
        if z == Infinity:
            if c == 0:
                return Infinity
            return a/c
        if a*d - b*c < 0:
            w = z.conjugate()  # Reverses orientation
        else:
            w = z
        if c*z + d == 0:
            return Infinity
        return (a*w + b) / (c*w + d)
    raise TypeError("A must be an invertible 2x2 matrix over the"
                    " complex numbers or a symbolic ring")

def angle_sign(self, other):  # UHP
    r"""
    Return the angle between any two given completed geodesics if
    they intersect.
    """
    (p1, p2) = [k.coordinates() for k in sorted_ideal_endpoints(self)]
    (q1, q2) = [k.coordinates() for k in sorted_ideal_endpoints(other)]
    if p1 != Infinity and  p2 != Infinity:  # geodesic not a straight line
        # So we send it to the geodesic with endpoints [0, oo]
        T = HyperbolicGeodesicUHP._crossratio_matrix(p1, (p1 + p2) / 2, p2)
    else:
        # geodesic is a straight line, so we send it to the geodesic
        # with endpoints [0,oo]
        if p1 == Infinity:
            T = HyperbolicGeodesicUHP._crossratio_matrix(p1, p2 + 1, p2)
        else:
            T = HyperbolicGeodesicUHP._crossratio_matrix(p1, p1 + 1, p2)
    # b1 and b2 are the endpoints of the image of other
    if T.determinant().sign() < 0:
        q1, q2 = q2, q1
    b1, b2 = [moebius_transform(T,k) for k in [q1, q2]]
    # If other is now a straight line...
    if (b1 == Infinity or b2 == Infinity):
        # then since they intersect, they are equal
        return 0
    assert b1 * b2 < 0
    return b1.sign()

class ArithGroup_fuchsian_generic(ArithGroup_generic):
    def get_word_rep(self,delta, P = None):
        if not self._is_in_order(delta):
            raise RuntimeError('delta (= %s) is not in order!'%delta)
        B = delta.parent()
        CC = ComplexField(300)
        if P is None:
            P = CC(90)/CC(100) * CC.gen()
        emb = self.get_archimedean_embedding(300)
        ngquats = self.ngquats
        gammas = self.gquats
        embgammas = self.embgquats
        pi = self.pi
        findex = self.findex
        fdargs = self.fdargs
        ans = []
        oldji = 0
        while delta != B(1):
            if delta == B(-1):
                if 'P' not in self._grouptype:
                    ans += self.minus_one_long
                delta = B(1)
                continue
            z0 = act_flt_in_disc(emb(delta),CC(0),P)
            az0 = CC(z0).argument()
            if az0 < fdargs[0]:
                az0 += 2*pi
            if az0 > fdargs[-1]:
                ji = findex[0]
                embgg = embgammas[ji]
                if act_flt_in_disc(embgg,z0,P).abs() > z0.abs():
                    ji = findex[1]
                    embgg = embgammas[ji]
            else:
                i = next((j for j,fda in enumerate(fdargs) if az0 < fda))
                ji = findex[i+1]
                embgg = embgammas[ji]
            z0 = act_flt_in_disc(embgg,CC(0),P)
            z0abs = z0.abs()
            if ji == -oldji:
                ji = next((j for j in range(-ngquats,0) + range(1,ngquats + 1) if j != -oldji and act_flt_in_disc(embgammas[j],z0,P).abs() < z0.abs()),None)
            if ji > 0:
                gg = gammas[ji]
                newcs = self.translate[ji]
            else:
                gg = gammas[-ji]**-1
                newcs = [-o for o in reversed(self.translate[-ji])]
            delta = gg * delta
            oldji = ji
            ans = ans + newcs
        if 'P' not in self._grouptype:
            delta1 = multiply_out(ans, self.Ugens, self.B(1))
            if delta1 != delta:
                ans.extend(self.minus_one_long)
        return ans

    def magma_word_problem(self, x):
        r'''
        Given a quaternion x, finds its decomposition in terms of the generators

        INPUT: x can be a list/vector of integers (giving the quaternion in terms of the basis for the order,
        or x can be a quaternion, in which case the conversion is done in the function.

        OUTPUT: A list representing a word in the generators
        '''
        x0 = x
        # If x is a quaternion, find the expression in the generators.
        if x in self.B: #.parent() is self.O or x.parent() is self.B:
            x = quaternion_to_magma_quaternion(self._B_magma, self.B(x))
        else:
            if len(x) != 4:
                raise ValueError('x (=%s) should be a list of length 4'%x)
            x = quaternion_to_magma_quaternion(self._B_magma,self.B(sum(a*b for a,b in zip(self.Obasis,x))))
        x_magma = self._G_magma(x)
        V = self.magma.WordProblem(x_magma).ElementToSequence()._sage_()
        delta1 = self.B(1)
        for v in V:
            delta1 = delta1 * self.Ugens[v - 1] if v > 0 else delta1 * self.Ugens[-v - 1]
        if delta1 != x0 and 'P' not in self._grouptype:
            V.extend(self.minus_one_long)
        return V

    def mat_list(self, x1, x2, check_fundom=True): # generic
        r'''
        Returns a list S of matrices such that the geodesic (x1, x2) is contained in the union
        of the translates s*D (with s in S) of the standard fundamental domain D.
        '''
        verbose('Calling mat_list with x1 = %s and x2 = %s'%(x1,x2))
        x1_orig = x1
        x2_orig = x2
        n = 0
        g = 1
        if check_fundom and not self.is_in_fundom(x1):
            t0, g = self.find_fundom_rep(x1)
            x1, x2 = t0, self(g**-1) * x2

        # Here we can assume that x1 is in the fundamental domain
        ans = [self(g)]
        while not self.is_in_fundom(x2):
            found = False
            for i, (v1, v2) in enumerate(self.fundamental_domain_data()):
                z = intersect_geodesic_arcs(v1, v2, x1, x2)
                if z is not None:
                    # We take a perturbation of z to avoid boundary problems
                    eps = 10**-4
                    z1, z2 = perturb_point_on_arc(x1, x2, z, eps)
                    if not self.is_in_fundom(z1):
                        z1, z2 = z2, z1
                    assert self.is_in_fundom(z1), 'z1 fails'
                    assert not self.is_in_fundom(z2), 'z2 fails'
                    for g in self.gquats[1:]:
                        t0 = self(g)**-1 * z2
                        if self.is_in_fundom(t0):
                            assert not found
                            found = True
                            x1 = t0
                            x2 = self(g)**-1 * x2
                            verbose('x1 = %s, x2 = %s'%(x1,x2))
                            ans.append(ans[-1] * self(g))
                            break
                    assert found,'Did not find any to move...'
                    break
            assert found,':-('
        return [o.quaternion_rep for o in ans]

    def _fix_sign(self,x,N):
        if self.F.signature()[1] == 1 or self.F.signature()[0] == 0:
            return x
        elif self.F.signature()[0] > 1:
            # raise NotImplementedError
            return x # FIXME this may not be correct
        emb = self.F.embeddings(RealField(100))[0]
        try:
            N = N.gens_reduced()[0]
        except AttributeError:
            pass
        if emb(x.reduced_norm()).sign() != emb(N).sign():
            x = x * self.non_positive_unit()
        if emb(x.reduced_norm()).sign() != emb(N).sign():
            raise RuntimeError('Error in fix_sign')
        return x

    def find_fundom_rep(self, z0_H, v0=None, return_alternative=False, max_iters=100): # generic -- Take z0 to the fundamental domain
        r'''
        Returns t0 and g such that g * t0 = z0_H, and t0 is in the fundamental domain
        '''
        B = self.B
        CC = z0_H.parent()
        if z0_H.imag() < 0:
            raise ValueError("z0_H must be in the upper half plane")
        verbose('Moving z0_H = %s to fundamental domain'%z0_H)
        emb = self.get_archimedean_embedding(CC.precision())
        P = CC(90)/CC(100) * CC.gen()
        Pconj = P.conjugate()
        z0 = (z0_H - P) / (z0_H - Pconj)
        ngquats = self.ngquats
        gammas = self.gquats
        embgammas = self.embgquats
        findex = self.findex
        fdargs = self.fdargs
        wd = []
        oldji = 0
        oldgg = B(1)
        gg = B(1)
        embgg = embgammas[1]**0
        delta = B(1)
        n_iters = 0
        t0 = z0_H
        t1 = z0_H
        while not self.is_in_fundom(t0) and not self.is_in_fundom(t1):
            n_iters += 1
            if n_iters >= max_iters:
                raise RuntimeError("Reached maximum number of iterations (%s)"%max_iters)
            az0 = CC(z0).argument()
            if az0 < fdargs[0]:
                az0 += 2 * self.pi
            if az0 > fdargs[-1]:
                ji = findex[0]
                embgg = embgammas[ji]
                if act_flt_in_disc(embgg,z0,P).abs() >= z0.abs():
                    ji = findex[1]
                    embgg = embgammas[ji]
            else:
                i = next((j for j,fda in enumerate(fdargs) if az0 <= fda), None)
                ji = findex[i+1]
                embgg = embgammas[ji]

            if ji is not None and ji == -oldji:
                my_range = range(-ngquats,0) + range(1,ngquats + 1)
                ji = next((j for j in my_range if j != -oldji and act_flt_in_disc(embgammas[j],z0,P).abs() <= z0.abs()),None)
            if ji is None or gammas[ji] * oldgg == -1:
                break
            else:
                embgg = embgammas[ji]
            gg = gammas[ji]
            delta = gg * delta
            z0 = act_flt_in_disc(embgg,z0,P)
            oldji, oldgg = ji, gg
            wd.append(gg)
            verbose('New g = %s\t delta = %s\t z0=%s'%(gg, delta, z0))
            t0 = self(delta) * z0_H
            t1 = self(wd[-1]**-1 * delta) * z0_H
        delta_inv = delta**-1
        if return_alternative:
            return (t0, delta_inv), (t1, delta_inv * wd[-1])
        else:
            if self.is_in_fundom(t0) or self.is_in_fundom_boundary(t0):
                return t0, delta_inv
            else:
                assert self.is_in_fundom(t1) or self.is_in_fundom_boundary(t1)
                return t1, delta_inv * wd[-1]

    def plot_fundamental_domain(self):
        return hyperbolic_polygon(self.fundamental_domain())

    @cached_method
    def fundamental_domain_interior_data(self): # generic
        UsideFD_magma = self._G_magma.get_magma_attribute('ShimFDSidepairs')
        length = len(UsideFD_magma)
        P = CC(0, 90.0/100.0) # A point inside the fundamental domain.
        in_interior = {}
        for v1, v2 in self.fundamental_domain_data():
            center, r2 = geodesic_circle(v1, v2, False)
            in_interior[(v1,v2)] = (center, r2, ((P - center).norm() < r2)) # The last argument encodes whether one needs to take the exterior or the interior of the geodesic circle.
        return in_interior

    @cached_method
    def fundamental_domain(self):
        return [ComplexField(1000)(o.Real().sage(), o.Imaginary().sage()) for o in self._G_magma.FundamentalDomain()]

    @cached_method
    def fundamental_domain_data(self):
        fdom = self.fundamental_domain()
        ans = [(fdom[i], fdom[i+1]) for i in range(len(fdom)-1)]
        ans.append((fdom[-1], fdom[0]))
        return ans

    def is_in_fundom(self, z):
        in_interior_data = self.fundamental_domain_interior_data()
        for v1, v2 in self.fundamental_domain_data():
            center, r2, in_interior = in_interior_data[(v1, v2)]
            if ((z - center).norm() < r2) != in_interior:
                return False
        return True

    def is_in_fundom_interior(self, z, tol = None):
        in_interior_data = self.fundamental_domain_interior_data()
        if tol is None:
            tol = 10**-5
        for v1, v2 in self.fundamental_domain_data():
            center, r2, in_interior = in_interior_data[(v1, v2)]
            if in_interior:
                if r2 - (z - center).norm() < tol:
                    return False
            else:
                if ((z - center).norm() - r2) < tol:
                    return False
        return True

    def is_in_fundom_exterior(self, z, tol = None):
        if self.is_in_fundom_interior(z, tol) or self.is_in_fundom_boundary(z, tol):
            return False
        else:
            return True

    def is_in_fundom_boundary(self, z, tol = None):
        in_interior_data = self.fundamental_domain_interior_data()
        if tol is None:
            tol = 10**-5
        for v1, v2 in self.fundamental_domain_data():
            center, r2, in_interior = in_interior_data[(v1, v2)]
            if (r2 - (z - center).norm()).abs() < tol:
                if is_in_open_interval(z.real(), v1.real(), v2.real(),0):
                    return True
        return False

    def get_archimedean_embedding(self,prec):
        r"""
        Returns an embedding of the quaternion algebra
        into the algebra of 2x2 matrices with coefficients in `RR`.

        INPUT:

        - prec -- Integer. The precision of the splitting.

        """
        I,J,K = self._splitting_at_infinity(prec)
        phi = self.F_into_RR
        def iota(q):
            R = I.parent()
            v = q.coefficient_tuple()
            return R(phi(v[0]) + phi(v[1]) * I + phi(v[2]) * J + phi(v[3]) * K)
        return iota

    def _splitting_at_infinity(self,prec):
        r"""
        Finds an embedding of the quaternion algebra
        into the algebra of 2x2 matrices with coefficients in `\RR`.

        INPUT:

        - prec -- Integer. The precision of the splitting.

        OUTPUT:

        - Matrices I, J, K giving the splitting.

        """
        if prec > self._prec_inf:
            wtime = walltime()
            verbose('Calling MatrixRing...')
            B_magma = self._B_magma
            f = self.magma.FuchsianMatrixRepresentation(B_magma.name(),Precision = prec,nvals = 1)
            verbose('Spent %s seconds in MatrixRing'%walltime(wtime))
            RR = RealField(prec)
            self._prec_inf=prec
            v = f.Image(B_magma.gen(1)).Vector()
            self._II_inf = matrix(RR,2,2,[v[i+1]._sage_() for i in xrange(4)])
            v = f.Image(B_magma.gen(2)).Vector()
            self._JJ_inf = matrix(RR,2,2,[v[i+1]._sage_() for i in xrange(4)])
            v = f.Image(B_magma.gen(3)).Vector()
            self._KK_inf = matrix(RR,2,2,[v[i+1]._sage_() for i in xrange(4)])

            RR = RealField(prec)
            rimg = f.Image(B_magma(sage_F_elt_to_magma(B_magma.BaseRing(),self.F.gen()))).Vector()
            rimg_matrix = matrix(RR,2,2,[rimg[i+1]._sage_() for i in xrange(4)])
            assert rimg_matrix.is_scalar()
            rimg = rimg_matrix[0,0]
            self.F_into_RR = self.F.hom([rimg],check = False)

        return self._II_inf, self._JJ_inf, self._KK_inf

class ArithGroup_rationalquaternion(ArithGroup_fuchsian_generic):
    def __init__(self,discriminant,level,info_magma = None,grouptype = None,magma = None, compute_presentation = True):
        assert grouptype in ['SL2','PSL2','PGL2'] # Need to find how to return the other groups with Voight's algorithm
        self._grouptype = grouptype
        self._compute_presentation = compute_presentation
        self.magma = magma
        self.F = QQ
        if isinstance(discriminant,list) or isinstance(discriminant,tuple):
            tmp = QuaternionAlgebra(discriminant[0],discriminant[1])
            self.abtuple = discriminant
            self.discriminant = ZZ(tmp.discriminant())
        else:
            self.discriminant = ZZ(discriminant)
        self.level = ZZ(level)

        self._prec_inf = -1

        self._init_magma_objects(info_magma)

        self.B = QuaternionAlgebra((self._B_magma.gen(1)**2)._sage_(),(self._B_magma.gen(2)**2)._sage_())
        assert self.B.discriminant() == self.discriminant, "Error while constructing quaternion algebra"
        self.O = self.B.quaternion_order([self.B([QQ(self._O_magma.ZBasis()[n+1].Vector()[m+1]) for m in xrange(4)]) for n in xrange(4)])
        self.Obasis = self.O.basis()
        self._O_discriminant = ZZ.ideal(self.O.discriminant())
        self.basis_invmat = matrix(QQ,4,4,[list(self.O.gen(n)) for n in xrange(4)]).transpose().inverse()
        if self._compute_presentation:
            self._G_magma = self.magma.FuchsianGroup(self._O_magma.name())
            FDom_magma = self._G_magma.FundamentalDomain() #self._D_magma.name()) # Debug
            self._U_magma,_,self._m2_magma = self._G_magma.Group(nvals = 3)
            self.Ugens = [magma_quaternion_to_sage(self.B,self._B_magma(self._m2_magma.Image(self._U_magma.gen(n+1))),self.magma) for n in xrange(len(self._U_magma.gens()))]

            Uside_magma = self._G_magma.get_magma_attribute('ShimGroupSidepairs')
            mside_magma = self._G_magma.get_magma_attribute('ShimGroupSidepairsMap')

            self.Uside = [magma_quaternion_to_sage(self.B,self._B_magma(self._m2_magma.Image(mside_magma.Image(g))),self.magma) for g in Uside_magma.Generators()]
            self.F_unit_offset = len(self.Ugens)

            # We initialize some attributes by calling this function stupidly
            self.magma.WordProblem(self._G_magma(1))

            gquats_magma = self._G_magma.get_magma_attribute('ShimGroupSidepairsQuats')
            self.ngquats = ZZ(len(gquats_magma[1]))
            emb = self.get_archimedean_embedding(300)
            self.gquats = translate_into_twosided_list([[magma_quaternion_to_sage(self.B,self._B_magma(gquats_magma[i+1][n+1].Quaternion()),self.magma) for n in xrange(len(gquats_magma[i+1]))] for i in xrange(2)])
            self.embgquats =  [None] + [emb(g) for g in self.gquats[1:]]

            self.pi = 4 * RealField(300)(1).arctan()
            self.findex = [ZZ(x._sage_()) for x in self._G_magma.get_magma_attribute('ShimGroupSidepairsIndex')]
            self.fdargs = [RealField(300)(x._sage_()) for x in self._G_magma.get_magma_attribute('ShimFDArgs')]

            self.minus_one_long = [ len(self.Ugens) + 1 ]
            self.Ugens.append(self.B(-1))
            self.translate = [None] + [self.magma_word_problem(g**-1) for g in self.gquats[1:]]
            self._gens = [ self.element_class(self,quaternion_rep = g, word_rep = [i+1],check = False) for i,g in enumerate(self.Ugens) ]
            temp_relation_words = [self._U_magma.Relations()[n+1].LHS().ElementToSequence()._sage_() for n in xrange(len(self._U_magma.Relations()))] + [ [len(self.Ugens),len(self.Ugens)] ]
            self._relation_words = []
            for rel in temp_relation_words:
                sign = multiply_out(rel, self.Ugens, self.B(1))
                if sign == 1 or 'P' in grouptype:
                    self._relation_words.append(rel)
                else:
                    newrel = rel + self.minus_one_long
                    assert multiply_out(newrel, self.Ugens, self.B(1)) == 1
                    self._relation_words.append(newrel)
        super(ArithGroup_rationalquaternion,self).__init__()

    def _repr_(self):
        return 'Arithmetic Group attached to rational quaternion algebra, disc = %s, level = %s'%(self.discriminant,self.level)

    def _init_magma_objects(self,info_magma = None): # Rational quaternions
        wtime = walltime()
        verbose('Calling _init_magma_objects...')
        if info_magma is None:
            QQ_magma = self.magma.RationalsAsNumberField()
            ZZ_magma = QQ_magma.MaximalOrder()
            if hasattr(self,'abtuple'):
                self._B_magma = self.magma.QuaternionAlgebra('%s'%QQ_magma.name(),self.abtuple[0],self.abtuple[1])
            else:
                self._B_magma = self.magma.QuaternionAlgebra('%s*%s'%(self.discriminant,ZZ_magma.name()))
            self._Omax_magma = self._B_magma.MaximalOrder()
            if self.level != ZZ(1):
                self._O_magma = self._Omax_magma.Order('%s*%s'%(self.level,ZZ_magma.name()))
            else:
                self._O_magma = self._Omax_magma
            self._D_magma = self.magma.UnitDisc(Precision = 300)
        else:
            ZZ_magma = info_magma._B_magma.BaseRing().Integers()
            self._B_magma = info_magma._B_magma
            self._Omax_magma = info_magma._Omax_magma
            if self.level != ZZ(1):
                self._O_magma = self._Omax_magma.Order('%s*%s'%(self.level,ZZ_magma.name()))
            else:
                self._O_magma = self._Omax_magma
            if self._compute_presentation:
                self._D_magma = self.magma.UnitDisc(Precision = 300)
            else:
                try:
                    self._D_magma = info_magma._D_magma
                except AttributeError:
                    pass
        self._F_magma = self._B_magma.BaseRing()
        verbose('Spent %s seconds in init_magma_objects'%walltime(wtime))

    def _quaternion_to_list(self,x):
        return (self.basis_invmat * matrix(QQ,4,1,x.coefficient_tuple())).list()

    # rationalquaternion
    def compute_quadratic_embedding(self,K):
        QQmagma = self.magma.Rationals()
        ZZmagma = self.magma.Integers()
        a,b = self.B.invariants()
        Btmp = self.magma.QuaternionAlgebra(QQmagma,a,b)
        def quat_to_mquat(x):
            v = list(x)
            return Btmp(v[0]) + sum(v[i+1]*Btmp.gen(i+1) for i in xrange(3))
        O_magma = self.magma.QuaternionOrder(ZZmagma,[quat_to_mquat(o) for o in self.Obasis])
        K_magma = self.magma.RadicalExtension(QQmagma,2,K.discriminant()) #self._B_magma.BaseField()
        OK_magma = K_magma.MaximalOrder()
        _,iota = self.magma.Embed(OK_magma,O_magma,nvals = 2)
        mu_magma = iota.Image(OK_magma(K_magma.gen(1)))
        Bgens = list(self.B.gens())
        return magma_quaternion_to_sage(self.B,Btmp(mu_magma),self.magma)

    # rationalquaternion
    def embed_order(self,p,K,prec,outfile = None,return_all = False, extra_conductor=1):
        r'''
        sage: from darmonpoints.sarithgroup import ArithGroup
        sage: G = ArithGroup(QQ,6,magma=Magma()) # optional - magma
        sage: f = G.embed_order(23,20) # optional - magma
        '''
        try:
            newobj = db('quadratic_embeddings_%s_%s.sobj'%(self.discriminant,self.level))
            mu = newobj[K.discriminant()]
        except IOError,KeyError:
            mu = self.compute_quadratic_embedding(K)

        w = K.maximal_order().ring_generators()[0]
        verbose('w is %s'%w)
        verbose('w.minpoly() = %s'%w.minpoly())
        QQp = Qp(p,prec)
        w_minpoly = w.minpoly().change_ring(QQp)
        Cp = QQp.extension(w_minpoly,names = 'g')
        coords = w.coordinates_in_terms_of_powers()
        r0,r1 = coords(K.gen())
        v0 = K.hom([Cp(r0)+Cp(r1)*Cp.gen()])
        try:
            phi = K.hom([mu])
        except TypeError:
            phi = K.hom([mu/2])
        fwrite('# d_K = %s, h_K = %s, h_K^- = %s'%(K.discriminant(),K.class_number(),len(K.narrow_class_group())),outfile)
        fwrite('# w_K satisfies: %s'%w.minpoly(),outfile)
        assert self._is_in_order(phi(w))

        iotap = self.get_embedding(prec)
        fwrite('# Local embedding B to M_2(Q_p) sends i to %s and j to %s'%(iotap(self.B.gens()[0]).change_ring(Qp(p,5)).list(),iotap(self.B.gens()[1]).change_ring(Qp(p,5)).list()),outfile)
        R = PolynomialRing(Cp,names = 'X')
        X = R.gen()

        eps0 = K.units()[0]**2
        eps = eps0
        while coords(eps)[1] % extra_conductor != 0:
            eps *= eps0
        gamma = self(phi(eps))

        a,b,c,d = iotap(gamma.quaternion_rep).list()
        DD = our_sqrt(Cp((a+d)**2 - 4))
        tau1 = (Cp(a - d) + DD) / Cp(2*c)
        tau2 = (Cp(a - d) - DD) / Cp(2*c)

        fwrite('# \cO_K to R_0 given by w_K |-> %s'%phi(w),outfile)
        fwrite('# gamma_psi = %s'%gamma,outfile)
        fwrite('# tau_psi = %s'%tau1,outfile)
        fwrite('# (where g satisfies: %s)'%w.minpoly(),outfile)
        if return_all:
            return gamma, tau1, tau2
        else:
            return gamma, tau1

    @cached_method(key = lambda self, N, use_magma, return_all, radius, max_elements : (self, N, return_all, max_elements))
    def element_of_norm(self,N,use_magma = True,return_all = False,radius = -1,max_elements = -1): # in rationalquaternion
        N = ZZ(N)
        force_sign = not 'P' in self._grouptype
        if use_magma:
            # assert return_all == False
            elt_magma = self._O_magma.ElementOfNorm(N * self._F_magma.Integers())
            candidate = self.B([magma_F_elt_to_sage(self.F,elt_magma.Vector()[m+1],self.magma) for m in xrange(4)])

            if force_sign:
                candidate = self._fix_sign(candidate,N)
            # assert candidate.reduced_norm() == N
            if return_all:
                return [candidate]
            else:
                return candidate
        else:
            v = list(self.Obasis)
            verbose('Doing long enumeration...')
            M = 0
            if return_all:
                all_candidates = []
            while M != radius:
                M += 1
                verbose('M = %s,radius = %s'%(M,radius))
                verbose('v = %s'%list(v))
                for a0,an in product(range(M),product(range(-M,M+1),repeat = len(v)-1)):
                    candidate = sum((ZZ(ai) * vi for ai,vi in  zip([a0]+list(an),v)),self.B(0))
                    if candidate.reduced_norm() == N:
                        if not return_all:
                            return candidate
                        else:
                            all_candidates.append(candidate)
                            if len(all_candidates) == max_elements:
                                verbose('Found %s elements of requested norm'%len(all_candidates))
                                return all_candidates
            if return_all:
                verbose('Found %s elements of requested norm'%len(all_candidates))
                return all_candidates
            else:
                raise RuntimeError('Not found')

    @cached_method(key = lambda self, radius : self)
    def non_positive_unit(self,radius = -1):
        v = self.Obasis
        verbose('Doing long enumeration...')
        M = 0
        while M != radius:
            M += 1
            verbose('M = %s,radius = %s'%(M,radius))
            for a0,an in product(range(M),product(range(-M+1,M),repeat = len(v)-1)):
                candidate = self.B(sum(ai*vi for ai,vi in  zip([a0]+list(an),v)))
                if candidate.reduced_norm() == -1:
                    return candidate

class ArithGroup_rationalmatrix(ArithGroup_generic):
    def __init__(self,level,info_magma = None,grouptype = None,magma = None, compute_presentation = True):
        from sage.modular.arithgroup.congroup_gammaH import GammaH_constructor
        assert grouptype in ['SL2','PSL2']
        self._grouptype = grouptype
        self._compute_presentation = compute_presentation
        self.magma = magma
        self.F = QQ
        self.discriminant = ZZ(1)
        try:
            self.level = ZZ(level)
            self._Gamma0_farey = GammaH_constructor(self.level, 0).farey_symbol()
        except TypeError:
            self.level = ZZ(level[0])
            self.nebentypus = level[1]
            self._Gamma0_farey = GammaH_constructor(self.level, level[1]).farey_symbol()
        self.F_units = []

        self._prec_inf = -1

        self.B = MatrixSpace(QQ,2,2)
        self.Obasis = [matrix(ZZ,2,2,v) for v in [[1,0,0,0],[0,1,0,0],[0,0,self.level,0],[0,0,0,1]]]
        self._O_discriminant = ZZ.ideal(self.level)

        self.Ugens = []
        self._gens = []
        temp_relation_words = []
        I = SL2Z([1,0,0,1])
        E = SL2Z([-1,0,0,-1])
        minus_one = None
        for i,g in enumerate(self._Gamma0_farey.generators()):
            newg = self.B([g.a(),g.b(),g.c(),g.d()])
            if newg == I:
                continue
            newg.set_immutable()
            self.Ugens.append(newg)
            self._gens.append(self.element_class(self,quaternion_rep = newg, word_rep = [i+1],check = False))
            if g.matrix()**2 == I.matrix():
                temp_relation_words.append([(i,2)])
                if minus_one is not None:
                    temp_relation_words.append([(i,-1)]+minus_one)
                minus_one = [(i,1)]
            elif g.matrix()**2 == E.matrix():
                temp_relation_words.append([(i,4)])
                if minus_one is not None:
                    temp_relation_words.append([(i,-2)]+minus_one)
                minus_one = [(i,2)]
            elif g.matrix()**3 == I.matrix():
                temp_relation_words.append([(i,3)])
            elif g.matrix()**3 == E.matrix():
                temp_relation_words.append([(i,6)])
                if minus_one is not None:
                    temp_relation_words.append([(i,-3)]+minus_one)
                minus_one = [(i,3)]
            else:
                assert g.matrix()**24 != I.matrix()
        self.F_unit_offset = len(self.Ugens)
        if minus_one is not None:
            self.minus_one_long = syllables_to_tietze(minus_one)
        self._relation_words = []
        for rel in temp_relation_words:
            sign = prod((self._gens[g].quaternion_rep**a for g,a in rel), z = self.B(1))
            if sign == self.B(1) or 'P' in grouptype:
                self._relation_words.append(syllables_to_tietze(rel))
            else:
                assert sign == self.B(-1)
                newrel = rel + tietze_to_syllables(self.minus_one_long)
                sign = prod((self._gens[g].quaternion_rep**a for g,a in newrel), z = self.B(1))
                assert sign == self.B(1)
                self._relation_words.append(syllables_to_tietze(newrel))
        super(ArithGroup_rationalmatrix,self).__init__()

    def _repr_(self):
        return 'Matrix Arithmetic Group of level = %s'%(self.level)
        a,b,c,d = x.list()
        return [a, b, QQ(c)/self.level, d]

    def _quaternion_to_list(self,x):
        return x.list()

    @cached_method
    def fundamental_domain(self):
        rho = (-1+AA(-3).sqrt())/2
        return [10**6 * AA(-1).sqrt(), rho, rho + 1]

    def get_archimedean_embedding(self,prec=None): # matrix
        r"""
        Returns an embedding of the quaternion algebra
        into the algebra of 2x2 matrices with coefficients in `\QQ_p`.

        INPUT:

        - prec -- Integer. The precision of the splitting.

        """
        return lambda x:x

    @cached_method
    def fundamental_domain_data(self):
        r'''
        Returns a list of triples (v_i, v_{i+1}, g_i),
        where the v_i are vertices of a fundamental domain D,
        and the g_i are matrices, such that
        (g_i * D) cap D = (v_i, v_{i+1}).
        '''
        ans = []
        rho = (-1+AA(-3).sqrt())/2
        S = self(matrix(ZZ,2,2,[0,-1,1,0]))
        T = self(matrix(ZZ,2,2,[1,1,0,1]))
        ans.append((Infinity, rho, T**-1))
        ans.append((rho, rho+1, S))
        ans.append((rho+1, Infinity, T))
        return ans

    def is_in_fundom(self, t,v0=None):
        if v0 is None:
            v0 = lambda x:x
        if t is Infinity or t == Infinity:
            return True
        else:
            return 2 * t.real_part().abs() <= 1 and t.norm() >= 1


    def find_fundom_rep(self, tau,v0=None): # rational matrix
        r'''
        Returns t0 and g such that g*t0 = tau, and t0 is in the fundamental domain
        '''
        if v0 is None:
            v0 = lambda x:x
        g = Matrix(ZZ,2,2,[1,0,0,1])
        if hasattr(tau, 'norm'):
            nrm = lambda x:x.norm()
        else:
            nrm = lambda x:x**2
        while not self.is_in_fundom(tau, v0):
            t = tau.real_part().floor()
            tau -= t
            if tau.real_part() > .5:
                tau -= 1
                g = g * Matrix(ZZ,2,2,[1,t+1, 0, 1])
            else:
                g = g * Matrix(ZZ,2,2,[1,t, 0, 1])
            if nrm(tau) < 1:
                tau = -1/tau
                g = g * Matrix(ZZ,2,2,[0,-1,1,0])
        return tau,g

    def mat_list(self, x1, x2, v0=None, check_fundom=True): # rationalmatrix
        r'''
        Returns a list S of matrices such that the geodesic (x1, g * x1) is contained in the union
        of the translates s*D (with s in S) of the standard fundamental domain D.
        '''
        if v0 is None:
            v0 = lambda x:x


        # We first deal with the case of x1 or x2 being Infinity
        if x1 == Infinity or x2 == Infinity:
            raise NotImplementedError

        verbose('Calling mat_list with x1 = %s and x2 = %s'%(x1,x2))
        x1_orig = x1
        x2_orig = x2
        n = 0
        g = 1
        if check_fundom and not self.is_in_fundom(x1):
            t0, g = self.find_fundom_rep(x1)
            x1, x2 = t0, self(g**-1) * x2
            verbose('x1 = %s, x2 = %s (move to fundom)'%(x1,x2))

        # Here we can assume that x1 is in the fundamental domain
        ans = [self(g)]
        while not self.is_in_fundom(x2):
            found = False
            for v1, v2, g in self.fundamental_domain_data():
                z = intersect_geodesic_arcs(v1, v2, x1, x2)
                if z is not None:
                    # We take a perturbation of z to avoid boundary problems
                    eps = 10**-4
                    z1, z2 = perturb_point_on_arc(x1, x2, z, eps)
                    if not self.is_in_fundom(z1):
                        z1, z2 = z2, z1
                    assert self.is_in_fundom(z1), 'z1 fails'
                    assert not self.is_in_fundom(z2), 'z2 fails'
                    t0 = g**-1 * z2
                    assert self.is_in_fundom(t0)
                    x1 = t0
                    x2 = g**-1 * x2
                    verbose('x1 = %s, x2 = %s'%(x1,x2))
                    ans.append(ans[-1] * g)
                    found = True
                    break
            assert found,':-('
        return ans

    def generate_wp_candidates(self,p,ideal_p,**kwargs):
        epsinv = matrix(QQ,2,2,[0,-1,p,0])**-1
        initial_wp = kwargs.get('initial_wp')
        if self.level == 1:
            try:
                ans = matrix(QQ,2,2,[0,-1,ideal_p.gens_reduced()[0],0])
            except AttributeError:
                ans = matrix(QQ,2,2,[0,-1,ideal_p,0])
            yield ans
        else:
            # Follow Atkin--Li
            if initial_wp is None:
                p = ideal_p
                m = self.level
                g,w,z = ZZ(p).xgcd(-m)
                ans = matrix(QQ,2,2,[p,1,p*m*z,p*w])
                all_initial = []
                for t in sorted(range(-8,7)):
                    g, tinv, k = ZZ(t).xgcd(-p * m)
                    if g == 1:
                        new_initial =  ans * matrix(QQ,2,2,[t, k, p*m, tinv])
                        all_initial.append(new_initial)
            else:
                all_initial = [initial_wp]
            for v1,v2 in cantor_diagonal(self.enumerate_elements(),self.enumerate_elements()):
                for tmp in all_initial:
                    yield  v1 * tmp * v2

    # rationalmatrix
    def embed_order(self,p,K,prec,orientation = None, use_magma = True,outfile = None, return_all = False, extra_conductor = 1, magma=None):
        from limits import _find_initial_embedding_list,find_optimal_embeddings,order_and_unit
        M = self.level
        extra_conductor = ZZ(extra_conductor)
        r = K.gen()
        w = K.maximal_order().ring_generators()[0]
        r0,r1 = w.coordinates_in_terms_of_powers()(K.gen())
        QQp = Qp(p,prec)
        Cp = QQp.extension(w.minpoly(),names = 'g')
        v0 = K.hom([r0+r1*Cp.gen()])
        W = find_optimal_embeddings(K,use_magma = use_magma, extra_conductor = extra_conductor, magma = magma)[0]
        OD,u = order_and_unit(K, extra_conductor)
        wD = OD.ring_generators()[0]
        wDvec = w.coordinates_in_terms_of_powers()(wD)
        WD = wDvec[0] + wDvec[1] * W
        tau, gamma = _find_initial_embedding_list(v0, M, WD, orientation, OD, u)[0]
        gamma.set_immutable()
        return self(gamma), v0(tau)

    def embed_order_legacy(self,p,K,prec,outfile = None,return_all = False):
        r'''
        '''
        from limits import _find_initial_embedding_list,find_optimal_embeddings,order_and_unit, find_the_unit_of

        verbose('Computing quadratic embedding to precision %s'%prec)
        mu = find_optimal_embeddings(K,use_magma = True, extra_conductor = 1)[-1]
        verbose('Finding module generators')
        w = module_generators(K)[1]
        verbose('Done')
        w_minpoly = w.minpoly().change_ring(Qp(p,prec))
        Cp = Qp(p,prec).extension(w_minpoly,names = 'g')
        wl = w.list()
        assert len(wl) == 2
        r0 = -wl[0]/wl[1]
        r1 = 1/wl[1]
        assert r0 + r1 * w == K.gen()
        padic_Kgen = Cp(r0)+Cp(r1)*Cp.gen()
        try:
            fwrite('# d_K = %s, h_K = %s, h_K^- = %s'%(K.discriminant(),K.class_number(),len(K.narrow_class_group())),outfile)
        except NotImplementedError: pass
        fwrite('# w_K satisfies: %s'%w.minpoly(),outfile)
        mu = r0 + r1*mu
        assert K.gen(0).trace() == mu.trace() and K.gen(0).norm() == mu.determinant()
        iotap = self.get_embedding(prec)
        a,b,c,d = iotap(mu).list()
        X = PolynomialRing(Cp,names = 'X').gen()
        tau1 = (Cp(a-d) + 2*padic_Kgen)/Cp(2*c)
        tau2 = (Cp(a-d) - 2*padic_Kgen)/Cp(2*c)
        assert (Cp(c)*tau1**2 + Cp(d-a)*tau1-Cp(b)) == 0
        assert (Cp(c)*tau2**2 + Cp(d-a)*tau2-Cp(b)) == 0
        u = find_the_unit_of(self.F,K)
        gammalst = u.list()
        assert len(gammalst) == 2
        gammaquatrep = self.B(gammalst[0]) + self.B(gammalst[1]) * mu
        verbose('gammaquatrep trd = %s and nrd = %s'%(gammaquatrep.trace(),gammaquatrep.determinant()))
        verbose('u trace = %s and unorm = %s'%(u.trace(),u.norm()))
        assert gammaquatrep.trace() == u.trace() and gammaquatrep.determinant() == u.norm()
        gammaq = gammaquatrep
        while True:
            try:
                gamma = self(gammaq)
                break
            except ValueError:
                gammaq *= gammaquatrep
        a, b, c, d = iotap(gamma.quaternion_rep).list()
        assert (c*tau1**2 + (d-a)*tau1 - b) == 0
        fwrite('# \cO_K to R_0 given by w_K |-> %s'%mu,outfile)
        fwrite('# gamma_psi = %s'%gamma,outfile)
        fwrite('# tau_psi = %s'%tau1,outfile)
        fwrite('# (where g satisfies: %s)'%w.minpoly(),outfile)
        if return_all:
            return gamma, tau1, tau2
        else:
            return gamma, tau1

    def get_word_rep(self,delta): # rationalmatrix
        level = self.level
        try:
            ans = list(self._Gamma0_farey.word_problem(SL2Z(delta.list()),output = 'standard'))
        except (RuntimeError,AssertionError):
            try:
                ans = list(self._Gamma0_farey.word_problem(SL2Z((-delta).list()),output = 'standard'))
            except (RuntimeError, AssertionError):
                print('Delta = %s'%delta)
                assert 0
        tmp = multiply_out(ans, self.Ugens, self.B(1))
        delta = SL2Z(delta.list())
        err = SL2Z(delta * SL2Z(tmp**-1))
        I = SL2Z([1,0,0,1])
        E = SL2Z([-1,0,0,-1])
        gens = self._Gamma0_farey.generators()
        if err == I:
            return self.check_word(delta.matrix(),ans)
        else:
            assert err == E
            ans = self.minus_one_long + ans
            return self.check_word(delta.matrix(),ans)

    @cached_method(key = lambda self, N, use_magma, return_all, radius, max_elements : (self, N, return_all))
    def element_of_norm(self,N,use_magma = False,return_all = False, radius = None, max_elements = None): # in rationalmatrix
        candidate = self.B([N,0,0,1])
        set_immutable(candidate)
        if return_all:
            return [candidate]
        else:
            return candidate

    def non_positive_unit(self):
        return self.B([1,0,0,-1])

    def _is_in_order(self,x):
        entries = x.list()
        if all([o.denominator() == 1 for o in entries]):
            if entries[2] % self.level == 0:
                if hasattr(self,'nebentypus'):
                    return ZZ(entries[0]) % self.level in self.nebentypus
                else:
                    return True
            else:
                return False
        else:
            return False

class ArithGroup_nf_generic(ArithGroup_generic):
    def __init__(self,base,a,b,level,info_magma = None,grouptype =  'PSL2',magma = None,timeout = 0, compute_presentation = True):
        self.magma = magma
        if base.signature()[1] == 0:
            self.algorithm = 'jv'
        elif base.signature()[1] == 1:
            self.algorithm = 'aurel'
        else:
            raise NotImplementedError('At most one complex place!')
        assert grouptype in ['SL2','PSL2','GL2','PGL2']
        self._prec_inf = -1

        self._grouptype = grouptype
        self._compute_presentation = compute_presentation
        self._elements_of_prime_norm = []
        self.F = base
        self.level = base.ideal(level)
        self.a,self.b = base(a),base(b)
        self.abtuple = (self.a, self.b)
        self.B = QuaternionAlgebra(self.F,self.a,self.b)
        self._init_magma_objects(info_magma)

        if self.B.invariants() == (1,1):
            i, j, k = self.B.gens()
            Pgen = level.gens_reduced()[0]
            tmpObasis_F = [(1 + i)/2, (j+k)/2, (Pgen/2)*(j-k), (1-i)/2]
            tmpObasis = [self.F.gen()**i * o  for o in tmpObasis_F for i in range(self.F.degree())]
            self._O_discriminant = self.F.ideal(self.B.discriminant()) * level
        else:
            magma_ZBasis = self._O_magma.ZBasis()
            tmpObasis = [magma_quaternion_to_sage(self.B,o,self.magma) for o in magma_ZBasis]
            self._O_discriminant = magma_F_ideal_to_sage(self.F,self._O_magma.Discriminant(),self.magma)
        self.Obasis = tmpObasis
        Obasis = [[u for o in elt.coefficient_tuple() for u in o.list()] for elt in tmpObasis]
        self.basis_invmat = matrix(QQ,4*self.F.degree(),4*self.F.degree(),Obasis).transpose().inverse()

        if self._compute_presentation:
            self._init_geometric_data(timeout = timeout)
        super(ArithGroup_nf_generic,self).__init__()

    def _repr_(self):
        return 'Arithmetic Group attached to quaternion algebra with a = %s, b = %s and level = %s'%(self.a,self.b,self.level)

    def _init_magma_objects(self,info_magma = None): # NF quaternion
        wtime = walltime()
        verbose('Calling _init_magma_objects...')
        if info_magma is None:
            Qx_magma = self.magma.PolynomialRing(self.magma.Rationals())
            xm = Qx_magma.gen(1)
            f = self.F.gen().minpoly()
            fmagma = sum([self.magma(c)*xm**i for c,i in zip(f.coefficients(),f.exponents())])
            if f.degree() == 1:
                FF_magma = self.magma.RationalsAsNumberField()
            else:
                FF_magma = self.magma.NumberField(fmagma,DoLinearExtension = True)
            self._F_magma = FF_magma
            OF_magma = FF_magma.Integers()
            am, bm = sage_F_elt_to_magma(self._F_magma,self.a),sage_F_elt_to_magma(self._F_magma,self.b)
            self._B_magma = self.magma.QuaternionAlgebra(FF_magma,am,bm)

            self._Omax_magma = self._B_magma.MaximalOrder()
            if self.level != self.F.ideal(1):
                self._O_magma = self._Omax_magma.Order(sage_F_ideal_to_magma(self._F_magma,self.level))
            else:
                self._O_magma = self._Omax_magma
            if self._compute_presentation:
                self._D_magma = self.magma.UnitDisc(Precision = 300)
        else:
            self._F_magma = info_magma._F_magma
            OF_magma = info_magma._F_magma.Integers()
            self._B_magma = info_magma._B_magma
            self._Omax_magma = info_magma._Omax_magma
            if self.level != self.F.ideal(1):
                M = sage_F_ideal_to_magma(self._F_magma,info_magma.level)
                self._O_magma = info_magma._Omax_magma.Order(M)
            else:
                self._O_magma = self._Omax_magma
            if self._compute_presentation:
                self._D_magma = self.magma.UnitDisc(Precision = 300)
            else:
                try:
                    self._D_magma = info_magma._D_magma
                except AttributeError:
                    pass
        if not hasattr(self,'_F_magma'):
            self._F_magma = self._B_magma.BaseRing()
        verbose('Spent %s seconds in init_magma_objects'%walltime(wtime))

    def _quaternion_to_list(self,x):
        xlist = [u for o in x.coefficient_tuple() for u in o.list()]
        V = (self.basis_invmat * matrix(QQ,4 * self.F.degree() ,1,xlist)).list()
        return [self.F(y) for y in izip(*[iter(V)]*self.F.degree())]

    def _is_in_order(self,x):
        return all([o.is_integral() for o in self._quaternion_to_list(x)])

    # nf_quaternion
    def compute_quadratic_embedding(self,K,return_generator = False):
        O_magma = self._O_magma
        F_magma = self._F_magma

        assert K.base_field() == self.F
        Fxmagma = self.magma.PolynomialRing(F_magma)
        Fxmagma.assign_names('x')
        xm = Fxmagma.gen(1)
        b = K.gen()
        f = b.minpoly()
        fm = sum([sage_F_elt_to_magma(self._F_magma,c) * xm**i for c,i in zip(f.coefficients(),f.exponents())])
        K_magma = self.magma.NumberField(fm)
        OK_magma = K_magma.MaximalOrder()
        verbose('Calling magma Embed function...')
        try:
            _,iota = self.magma.Embed(OK_magma,O_magma,nvals = 2)
        except RuntimeError:
            print('An error ocurred!')
            print('OK_magma = %s'%OK_magma)
            print('O_magma ='%O_magma)
            raise RuntimeError('Error while computing quadratic embedding')
        verbose('Calling magma Embed function done!')
        wm = K_magma(OK_magma.Basis()[2])
        w = K(magma_F_elt_to_sage(self.F,wm[1],self.magma) + magma_F_elt_to_sage(self.F,wm[2],self.magma) * b)
        ans = magma_integral_quaternion_to_sage(self.B,O_magma,F_magma,iota.Image(OK_magma(K_magma.gen(1))),self.magma)
        assert ans.reduced_norm() == K.gen().norm(self.F) and ans.reduced_trace() == K.gen().trace(self.F)
        ans = self.B(ans)
        if return_generator:
            verbose('w = %s, minpoly = %s'%(w,w.minpoly()))
            assert w in K.maximal_order()
            return ans,w
        else:
            return ans

    # nf_quaternion
    def embed_order(self,p,K,prec,outfile = None,return_all = False, extra_conductor = 1):
        r'''
        '''
        verbose('Computing quadratic embedding to precision %s'%prec)
        mu = self.compute_quadratic_embedding(K,return_generator = False)
        verbose('Finding module generators')
        w = module_generators(K)[1]
        verbose('Done')
        w_minpoly = PolynomialRing(Qp(p,prec),names = 'x')([self._F_to_local(o) for o in w.minpoly().coefficients(sparse=False)])
        verbose('w_minpoly = %s'%w_minpoly)
        Cp = Qp(p,prec).extension(w_minpoly,names = 'g')
        verbose('Cp is %s'%Cp)
        wl = w.list()
        assert len(wl) == 2
        r0 = -wl[0]/wl[1]
        r1 = 1/wl[1]
        assert r0+r1*w == K.gen()
        padic_Kgen = Cp(self._F_to_local(r0))+Cp(self._F_to_local(r1))*Cp.gen()
        try:
            fwrite('# d_K = %s, h_K = %s, h_K^- = %s'%(K.discriminant(),K.class_number(),len(K.narrow_class_group())),outfile)
        except NotImplementedError: pass
        fwrite('# w_K satisfies: %s'%w.minpoly(),outfile)
        assert K.gen(0).trace(K.base_ring()) == mu.reduced_trace() and K.gen(0).norm(K.base_ring()) == mu.reduced_norm()

        iotap = self.get_embedding(prec)
        fwrite('# Local embedding B to M_2(Q_p) sends i to %s and j to %s'%(iotap(self.B.gens()[0]).change_ring(Qp(p,5)).list(),iotap(self.B.gens()[1]).change_ring(Qp(p,5)).list()),outfile)

        found = False
        coords = lambda x:K(x).list() #K.gen().coordinates_in_terms_of_powers()
        phi = K.hom([mu, self.B(self.F.gen())],check=False)
        u0 = find_the_unit_of(self.F,K)
        assert u0.is_integral() and (1/u0).is_integral()
        u = u0
        # Deal with nontrivial conductor
        while not self.F.ideal(extra_conductor).divides(self.F.ideal(coords(u)[1])):
            u *= u0
        gammalst = coords(u)
        verbose('gammalst = %s (length = %s)'%(gammalst,len(gammalst)))
        assert len(gammalst) == 2
        gammaquatrep = self.B(gammalst[0]) + self.B(gammalst[1]) * mu # phi(u)
        verbose('gammaquatrep trd = %s and nrd = %s'%(gammaquatrep.reduced_trace(),gammaquatrep.reduced_norm()))
        assert gammaquatrep.reduced_trace() == u.trace(self.F) and gammaquatrep.reduced_norm() == u.norm(self.F)

        gammaq = gammaquatrep
        while True:
            try:
                gamma = self(gammaq)
                break
            except ValueError:
                gammaq *= gammaquatrep

        a,b,c,d = iotap(gamma.quaternion_rep).list()
        DD = our_sqrt(Cp((a+d)**2 - 4))
        tau1 = (Cp(a - d) + DD) / Cp(2*c)
        tau2 = (Cp(a - d) - DD) / Cp(2*c)
        fwrite('# \cO_K to R_0 given by w_K |-> %s'%mu,outfile)
        fwrite('# gamma_psi = %s'%gamma,outfile)
        fwrite('# tau_psi = %s'%tau1,outfile)
        fwrite('# (where g satisfies: %s)'%w.minpoly(),outfile)

        if return_all:
            return gamma, tau1, tau2
        else:
            return gamma, tau1

    def element_of_prime_norm(self,max_norm,radius = -1):
        v = self.Obasis
        verbose('Doing long enumeration...')
        M = 0
        F = self.B.base_ring()
        while M != radius:
            M += 1
            verbose('M = %s,radius = %s'%(M,radius))
            for a0,an in product(range(M),product(range(-M+1,M),repeat = len(v)-1)):
                candidate = self.B(sum(ai*vi for ai,vi in  zip([a0]+list(an),v)))
                candidate_norm = F(candidate.reduced_norm())
                if candidate_norm == 0:
                    continue
                if F.ideal(candidate_norm).is_prime() and candidate_norm.norm().abs() < max_norm:
                    self._elements_of_prime_norm.append(candidate)
                    yield candidate

    @cached_method(key = lambda self, N, use_magma, return_all, radius, max_elements: (self, N, return_all, max_elements))
    def element_of_norm(self,N,use_magma = True,return_all = False,radius = -1,max_elements = -1): # in nf_quaternion
        Nideal = self.F.ideal(N)
        try:
            N = N.gens_reduced()[0]
        except AttributeError:
            pass
        force_sign = not 'P' in self._grouptype
        if return_all and radius < 0 and max_elements < 0:
            raise ValueError('Radius must be positive')

        x = QQ['x'].gen()
        B = self.B
        F = self.B.base_ring()
        try:
            K1 = F.extension(x*x - B.invariants()[0], names = 'y1')
            phi1 = lambda z: list(z)[0] + list(z)[1] * B.gen(0)
            NK1f = K1.ideal(Nideal.gens_reduced()[0]).factor()
        except ValueError:
            NK1f = []
        try:
            K2 = F.extension(x*x - B.invariants()[1], names = 'y2')
            phi2 = lambda z: list(z)[0] + list(z)[1] * B.gen(1)
            NK2f = K2.ideal(Nideal.gens_reduced()[0]).factor()
        except ValueError:
            NK2f = []
        found_candidate = False
        if len(NK1f) == 2:
            gr = NK1f[0][0].gens_reduced()
            if len(gr) == 1:
                candidate = phi1(gr[0])
                if self._is_in_order(candidate):
                    found_candidate = True
        if not found_candidate and len(NK2f) == 2:
            gr = NK2f[0][0].gens_reduced()
            if len(gr) == 1:
                candidate = phi2(gr[0])
                if self._is_in_order(candidate):
                    found_candidate = True
        if not found_candidate:
            elt_magma = self._O_magma.ElementOfNorm(sage_F_ideal_to_magma(self._F_magma,Nideal))
            candidate = magma_quaternion_to_sage(self.B,elt_magma,self.magma)
        if force_sign:
            candidate = self._fix_sign(candidate,N)
        if return_all:
            return [candidate]
        else:
            return candidate

    @cached_method(key = lambda self, radius: self)
    def non_positive_unit(self,radius = -1):
        v = self.Obasis
        verbose('Doing long enumeration...')
        M = 0
        ideal_one = self.F.ideal(1)
        while M != radius:
            M += 1
            verbose('M = %s,radius = %s'%(M,radius))
            for a0,an in product(range(M),product(range(-M+1,M),repeat = len(v)-1)):
                candidate = self.B(sum(ai*vi for ai,vi in  zip([a0]+list(an),v)))
                if self.F.ideal(candidate.reduced_norm()) == ideal_one and candidate.reduced_norm() != 1:
                    return candidate

class ArithGroup_nf_fuchsian(ArithGroup_nf_generic, ArithGroup_fuchsian_generic):
    def _init_geometric_data(self, timeout = 0): # nf quaternion
        if timeout != 0:
            raise NotImplementedError("Timeout functionality not implemented yet")

        self._G_magma = self.magma.FuchsianGroup(self._O_magma.name())
        FDom_magma = self._G_magma.FundamentalDomain() #self._D_magma.name()) # Debug
        self._U_magma,_,self._m2_magma = self._G_magma.Group(nvals = 3)

        self.Ugens = [magma_quaternion_to_sage(self.B,self._B_magma(self._m2_magma.Image(self._U_magma.gen(n+1))),self.magma) for n in xrange(len(self._U_magma.gens()))]

        Uside_magma = self._G_magma.get_magma_attribute('ShimGroupSidepairs')
        mside_magma = self._G_magma.get_magma_attribute('ShimGroupSidepairsMap')
        UsideFD_magma = self._G_magma.get_magma_attribute('ShimFDSidepairs')

        self.Uside = [magma_quaternion_to_sage(self.B,self._B_magma(self._m2_magma.Image(mside_magma.Image(g))),self.magma) for g in Uside_magma.Generators()]

        # We initialize some attributes by calling this function stupidly
        self.magma.WordProblem(self._G_magma(1))

        gquats_magma = self._G_magma.get_magma_attribute('ShimGroupSidepairsQuats')
        self.ngquats = ZZ(len(gquats_magma[1]))
        emb = self.get_archimedean_embedding(300)
        self.gquats = translate_into_twosided_list([[magma_quaternion_to_sage(self.B,self._B_magma(gquats_magma[i+1][n+1].Quaternion()),self.magma) for n in xrange(len(gquats_magma[i+1]))] for i in xrange(2)])
        self.embgquats =  [None] + [emb(g) for g in self.gquats[1:]]

        self.pi = 4 * RealField(300)(1).arctan()
        self.findex = [ZZ(x._sage_()) for x in self._G_magma.get_magma_attribute('ShimGroupSidepairsIndex')]
        self.fdargs = [RealField(300)(x._sage_()) for x in self._G_magma.get_magma_attribute('ShimFDArgs')]

        self.minus_one_long = [ len(self.Ugens) + 1 ]
        self.Ugens.append(self.B(-1))

        self.translate = [None] + [self.magma_word_problem(g**-1) for g in self.gquats[1:]]

        self._gens = [ self.element_class(self,quaternion_rep = g, word_rep = [i+1],check = False) for i,g in enumerate(self.Ugens) ]

        temp_relation_words = [self._U_magma.Relations()[n+1].LHS().ElementToSequence()._sage_() for n in xrange(len(self._U_magma.Relations()))] + [ [len(self.Ugens), len(self.Ugens)] ]

        self._relation_words = []
        for rel in temp_relation_words:
            sign = multiply_out(rel,self.Ugens)
            # assert sign.abs() == 1
            if sign == 1 or 'P' in self._grouptype:
                self._relation_words.append(rel)
            else:
                newrel = rel + self.minus_one
                assert multiply_out(newrel, self.Ugens, self.B(1)) == 1
                self._relation_words.append(newrel)

class ArithGroup_nf_kleinian(ArithGroup_nf_generic):
    def _init_geometric_data(self,prec = 100,periodenum = 20, timeout = 0):
        verbose('Computing normalized basis')
        if 'GL' in self._grouptype:
            # raise NotImplementedError,'This implementation has bugs'
            grouptype = '"Units"'
        else:
            grouptype = '"NormOne"'
            assert 'SL' in self._grouptype
        verbose('Seed = %s'%self.magma.eval('GetSeed()'))
        verbose(' O = %s'%self._O_magma)
        verbose(' Basis = %s'%self._O_magma.Basis())
        verbose('Grouptype = %s, prec = %s, periodenum = %s, timeout = %s'%(grouptype,prec, periodenum, timeout))

        _,f,e = self._O_magma.NormalizedBasis(GroupType = grouptype, nvals = 3, pr = prec, PeriodEnum = periodenum, max_time = timeout)
        verbose('Done normalizedbasis')
        if f == self.magma(False):
            raise RuntimeError("Timed out (%s sec) in NormalizedBasis"%timeout)
        matlist = self.magma.GetMatrixList(f)

        self._fundom_data = []
        verbose('Getting precision from Magma')
        try:
            self._RR = RR = RealField((len(str(f[1].Radius)) * RealField(20)(10).log()/RealField(20)(2).log()).ceil()-13)
        except:
            self._RR = RR = RealField(100)
        verbose('Getting precision done')
        prec = RR.precision()
        CC = ComplexField(prec)
        all_complex_embs = [o for o in self.F.embeddings(CC) if o(self.F.gen()).imag() != 0]
        assert len(all_complex_embs) == 2
        vC = all_complex_embs[0]
        tmp = self.magma.InfinitePlaces(self._F_magma)[1 + self.F.signature()[0]]
        if (vC(self.F.gen(0)).imag() * self._F_magma.gen(1).Evaluate(tmp).Im()._sage_()) < 0:
            vC = all_complex_embs[1]
            assert (vC(self.F.gen(0)).imag() * self._F_magma.gen(1).Evaluate(tmp).Im()._sage_()) > 0
        self._vC = vC
        self._HH = QuaternionAlgebra(RR,-1,-1)
        ih,jh,kh = self._HH.gens()
        self._Pmat, self._Pmatinv = JtoP(self._HH,MatrixSpace(CC,2,2))
        i,j,k  = self.B.gens()
        centerlist = sage_eval(self.magma.eval('[%s[i]`Center : i in [1..%s]]'%(f.name(),len(f))),{'i': ih, 'j': jh})
        radiuslist = sage_eval(self.magma.eval('[%s[i]`Radius : i in [1..%s]]'%(f.name(),len(f))))
        matlist = sage_eval(self.magma.eval('[%s[i] : i in [1..%s]]'%(matlist.name(),len(f))),{'i' : ih, 'j': jh, 'k': kh})
        self._fundom_data = [(self._HH(c),RR(r),Matrix(self._HH,2,2,m)) for c,r,m in zip(centerlist,radiuslist,matlist)]

        verbose('Computing presentation')
        G,gens = f.Presentation(e,self._O_magma,nvals = 2)
        Hm,GtoHm = self.magma.ReduceGenerators(G,nvals = 2)
        r = self.F.gen()
        i,j,k = self.B.gens()
        chunk_length = 10
        ngens = len(gens)
        assert ngens == len(G.gens())
        nchunks = (QQ(ngens)/QQ(chunk_length)).ceil()
        verbose('Done ReduceGenerators. Now calculating inverse iso for %s generators'%len(gens))
        tmp_quaternions = []
        self._simplification_iso = []
        for tt in xrange(nchunks):
            verbose('... %s/%s ...'%(tt+1,nchunks))
            i0 = tt * chunk_length + 1
            i1 = min((tt+1) * chunk_length,ngens)
            newvec = sage_eval(self.magma.eval('[ElementToSequence(Image(%s,%s.i)) : i in [%s..%s]]'%(GtoHm.name(),G.name(),i0,i1)))
            self._simplification_iso.extend(newvec)
            tmp_quaternions.extend(sage_eval(self.magma.eval('[%s[i] : i in [%s..%s]]'%(gens.name(),i0,i1)).replace('$.1','r'),{'r':r, 'i':i, 'j':j, 'k':k}))

        assert len(self._simplification_iso) == len(self._fundom_data), "Simplification iso and facerels have different lengths (%s != %s)"%(len(self._simplification_iso),len(self._fundom_data))
        verbose('Done inverse isomorphism. Now calculating Ugens for %s generators'%len(Hm.gens()))
        self.Ugens = []
        wrds = sage_eval(self.magma.eval('[ElementToSequence(%s!(%s.i)) : i in [1..%s]]'%(G.name(),Hm.name(),len(Hm.gens()))))
        for wd in wrds:
            self.Ugens.append(multiply_out(wd, tmp_quaternions, self.B(1)))
        verbose('Done calculating Ugens. Now initializing relations')
        if 'P' not in self._grouptype:
            self.F_units = self.F.unit_group()
            self.F_unit_offset = len(self.Ugens)
            self.Ugens.extend([self.B(self.F(u)) for u in self.F_units.gens()])
            temp_relation_words = [Hm.Relations()[n+1].LHS().ElementToSequence()._sage_() for n in xrange(len(Hm.Relations()))] + [ [self.F_unit_offset + i + 1] * ZZ(u.multiplicative_order()) for i,u in enumerate(self.F_units.gens()) if u.multiplicative_order() != Infinity]
            self._relation_words = []
            for rel in temp_relation_words:
                remaining_unit = self.F_units(self.F(multiply_out(rel, self.Ugens, self.B(1))))
                assert remaining_unit.multiplicative_order() != Infinity
                ulist = remaining_unit.exponents()
                newrel = rel + syllables_to_tietze([(self.F_unit_offset + i,a) for i,a in enumerate(ulist) if a != 0 ])
                assert multiply_out(newrel, self.Ugens, self.B(1)) == 1
                self._relation_words.append(newrel)
        else:
            self._relation_words = [Hm.Relations()[n+1].LHS().ElementToSequence()._sage_() for n in xrange(len(Hm.Relations()))]
        verbose('Done initializing relations. Now generators...')
        self._gens = [self.element_class(self,quaternion_rep = g, word_rep = [i+1],check = False) for i, g in enumerate(self.Ugens)]
        verbose('Done initializing generators')

    def _kleinianmatrix(self,gamma):
        B = gamma.parent()
        K = gamma.parent().base_ring()
        CC = ComplexField(self._RR.precision())
        vC = self._vC
        aa,bb = [vC(o) for o in B.invariants()]
        sa = aa.sqrt()
        bsa = bb * sa
        P, Pinv = self._Pmat, self._Pmatinv
        x1,x2,x3,x4 = [vC(o) for o in gamma.coefficient_tuple()]
        hi = self._HH.gen(0)
        phi = lambda x:self._HH(x.real()) + hi * x.imag()
        m = Pinv * Matrix(CC,2,2,[x1 + x2*sa, x3 + x4*sa, x3*bb - x4*bsa, x1- x2*sa])* P
        if gamma.reduced_norm() != 1:
            scal = 1/m.determinant().sqrt()
            m *= scal
        a,b,c,d = m.apply_map(phi).list()
        hj = self._HH.gen(1)
        A = ((a+d.conjugate()) + (b-c.conjugate())*hj)
        B = ((b+c.conjugate()) + (a-d.conjugate())*hj)
        C = ((c+b.conjugate()) + (d-a.conjugate())*hj)
        D = ((d+a.conjugate()) + (c-b.conjugate())*hj)
        return Matrix(self._HH,2,2,[A,B,C,D])

    @cached_method
    def fundamental_domain(self):
        raise NotImplementedError

    def get_word_rep(self,gamma):
        HH = self._HH
        R = HH.base_ring()
        boundary = self._fundom_data
        eps = 2**-(R(HH.base_ring().precision())/R(2))
        #verbose('eps = %s'%eps)
        correct = False
        B = self.B
        deltaword = []
        gammainv = gamma**-1
        while not correct:
            z = HH(0)
            mat_gamma = self._kleinianmatrix(gammainv)
            gammaz = act_H3(mat_gamma,z)
            if len(boundary) == 0:
                raise RuntimeError('Empty boundary')
            lengthw = 0
            delta = B(1)
            while True:
                d = R(1)
                i0 = None
                for i,(center, radius, mat) in enumerate(boundary):
                    d1 = sum((o**2 for o in (gammaz - center).coefficient_tuple())) / radius**2
                    if d >= (1+eps)*d1:
                        d = d1
                        i0 = i
                        break # This might yield longer words, but should be faster!
                if i0 is None:
                    break
                gammaz = act_H3(boundary[i0][2],gammaz)
                deltaword.append(i0+1)
                lengthw += 1
            correct = ( -(sum((o**2 for o in gammaz.coefficient_tuple()))).log(10) > 5.0)
            if not correct:
                verbose('Error in word problem:')
                verbose('gamma = %s'%gamma)
                verbose('err = %s'%-(sum((o**2 for o in gammaz.coefficient_tuple()))))
                raise RuntimeError('Error in word problem from Aurel 1')
        deltaword.reverse()
        try:
            c = sum((list(self._simplification_iso[o-1]) for o in deltaword),[])
        except IndexError:
            raise RuntimeError('Error in word problem from Aurel 2')
        return c

class ArithGroup_matrix_generic(ArithGroup_generic):
    def find_matrix_from_cusp(self, cusp):
        r'''
        Returns a matrix gamma and a cusp representative modulo Gamma0(N) (c2:d2),
        represented as a matrix (a,b;c,d), such that gamma * cusp = (c2:d2).
        '''
        a, c = cusp
        reduction_table, _ = self.cusp_reduction_table()
        P = self.get_P1List()
        if hasattr(P.N(),'number_field'):
            K = P.N().number_field()
        else:
            K = QQ

        # Find a matrix g = [a,b,c,d] in SL2(O_K) such that g * a/c = oo
        # Define (c1:d1) to be the rep in P1(O_K/N) such that (c1:d1) == (c:d).
        if c == 0: ## case cusp infinity: (a,c) should equal (1,0)
            a = 1
            g = Matrix(2,2,[1,0,0,1])
            c1, d1 = P.normalize(0, 1)
        else:
            if K == QQ:
                g0, d, b = ZZ(a).xgcd(-c)
                if g0 != 1:
                    a /= g0
                    c /= g0
            else:
                """
                Compute gcd if a,c are coprime in F, and x,y such that
                    ax + cy = 1.
                """
                if a.parent() != c.parent():
                    raise ValueError('a,c not in the same field.')
                if a.gcd(c) != 1:
                    raise ValueError('a,c not coprime.')

                d = next(o for o in K.ideal(c).residues() if a * o - 1 in K.ideal(c))
                b = (a * d - 1) / c

            g = Matrix(2,2,[[d,-b],[-c,a]]) # the inverse
            c1, d1 = P.normalize(c, d)
        assert g.determinant() == 1

        A, T = reduction_table[(c1,d1)]
        gamma = A.parent()(A * T * g)
        return gamma, A

    def compute_cusp_stabiliser(self,cusp_matrix):
        """
        Compute (a finite index subgroup of) the stabiliser of a cusp 
        in Q or a quadratic imaginary field.

        We know the stabiliser of infinity is given by matrices of form 
        (u, a; 0, u^-1), so a finite index subgroup is generated by (1, alpha; 0, 1)
        and (1, 1; 0, 1) for K = Q(alpha). Given the cusp, we use a matrix
        sending infinty to that cusp, and the conjugate by it, before taking powers
        to ensure the result is integral and lies in Gamma_0(N).

        Input: 
            - a cusp (in matrix form: as output by cusp_set)
            - N (the level: an ideal in K).

        Outputs a list of the generators (as matrices).
        """

        P = self.get_P1List()
        if hasattr(P.N(),'number_field'):
            K = P.N().number_field()
            ## Write down generators of a finite index subgroup in Stab_Gamma(infinity)
            infinity_gens = [matrix(K,[[1,1],[0,1]]), matrix(K,[[1,K.gen()],[0,1]])]
            N_ideal = P.N()
        else:
            K = QQ
            infinity_gens = [matrix([[1,1],[0,1]])]
            N_ideal = ZZ.ideal(P.N())

        ## Initilise (empty) list of generators of Stab_Gamma(cusp)
        cusp_gens = []

        ## Loop over all the generators of stab at infinity, conjugate into stab at cusp
        for T in infinity_gens:
            T_conj = cusp_matrix * T * cusp_matrix.adjugate()
            gen = T_conj

            ## Now take successive powers until the result is in Gamma_0(N)
            while not gen[1][0] in N_ideal:
                 gen *= T_conj

            ## We've found an element in Stab_Gamma(cusp): add to our list of generators
            cusp_gens.append(gen)
        return cusp_gens

    @cached_method
    def cusp_reduction_table(self):
        r'''
        Returns a dictionary and the set of cusps.

        Assumes we have a finite set surjecting to the cusps (namely, P^1(O_F/N)). Runs through
        and computes a subset which represents the cusps, and shows how to go from any element 
        of P^1(O_F/N) to the chosen equivalent cusp.

        Takes as input the object representing P^1(O_F/N), where F is a number field
        (that is possibly Q), and N is some ideal in the field.  Runs the following algorithm:
                - take a remaining element C = (c:d) of P^1(O_F/N);
                - add this to the set of cusps, declaring it to be our chosen rep;
                - run through every translate C' = (c':d') of C under the stabiliser of infinity, and
                        remove this translate from the set of remaining elements;
                - store the matrix T in the stabiliser such that C' * T = C (as elements in P^1)
                        in the dictionary, with key C'.
        '''
        P = self.get_P1List()
        if hasattr(P.N(),'number_field'):
            K = P.N().number_field()
        else:
            K = QQ

        from sage.modular.modsym.p1list_nf import lift_to_sl2_Ok
        from sage.modular.modsym.p1list import lift_to_sl2z
        ## Define new function on the fly to pick which of Q/more general field we work in
        ## lift_to_matrix takes parameters c,d, then lifts (c:d) to a 2X2 matrix over the NF representing it
        lift_to_matrix = lambda c, d: lift_to_sl2z(c,d,P.N()) if K.degree() == 1 else lift_to_sl2_Ok(P.N(), c, d)

        ## Put all the points of P^1(O_F/N) into a list; these will corr. to our dictionary keys
        remaining_points = set(list(P)) if K == QQ else set([c.tuple() for c in P])
        reduction_table = {}
        cusp_set = []

        initial_points = len(remaining_points)

        ## Loop over all points of P^1(O_F/N)
        while len(remaining_points) > 0:
            ## Pick a new cusp representative
            c = remaining_points.pop()
            update_progress(1 - float(len(remaining_points)) / float(initial_points), "Finding cusps...")
            ## c is an MSymbol so not hashable. Create tuple that is
            ## Represent the cusp as a matrix, add to list of cusps, and add to dictionary
            new_cusp = Matrix(2,2,lift_to_matrix(c[0], c[1])) 
            new_cusp.set_immutable()
            cusp_set.append(new_cusp)
            reduction_table[c]=(new_cusp,matrix(2,2,1)) ## Set the value to I_2
            ## Now run over the whole orbit of this point under the stabiliser at infinity.
            ## For each elt of the orbit, explain how to reduce to the chosen cusp.

            ## Run over lifts of elements of O_F/N:
            if K == QQ:
                residues = Zmod(P.N())
                units = [1, -1]
            else:
                residues = P.N().residues()
                units = K.roots_of_unity()

            for hh in residues:
                h = K(hh) ## put into the number field
                ## Run over all finite order units in the number field
                for u in units:
                    ## Now have the matrix (u,h; 0,u^-1).
                    ## Compute the action of this matrix on c
                    new_c = P.normalize(u * c[0], u**-1 * c[1] + h * c[0])
                    if K != QQ: 
                        new_c = new_c.tuple()
                    if new_c not in reduction_table:
                        ## We've not seen this point before! But it's equivalent to c, so kill it!
                        ## (and also store the matrix we used to get to it)
                        remaining_points.remove(new_c)
                        T = matrix(2,2,[u,h,0,u**-1]) ## we used this matrix to get from c to new_c
                        reduction_table[new_c]=(new_cusp, T) ## update dictionary with the new_c + the matrix
                        if K != QQ:
                            assert P.normalize(*(vector(c) * T)).tuple() == new_c ## sanity check
                        else:
                            assert P.normalize(*(vector(c) * T)) == new_c ## sanity check

        return reduction_table, cusp_set

    @cached_method
    def get_P1List(self):
        """
        Generates the projective line of O_F/N, where N is an ideal specified
        in the input, or computed from a parent object (e.g. arithmetic group).
        """
        N = self.level

        ## Return object representing Projective line over O_F/N
        if hasattr(N,'number_field'): ## Base field not Q
            from sage.modular.modsym.p1list_nf import P1NFList
            return P1NFList(N)
        else:   ## Base field Q
            from sage.modular.modsym.p1list import P1List
            return P1List(N)

class ArithGroup_nf_matrix_new(ArithGroup_matrix_generic, ArithGroup_nf_generic):
    def __init__(self,base,level,level0 = None, info_magma = None,grouptype =  'PSL2',magma = None,timeout = 0, compute_presentation = None):
        assert level0 is None
        verbose('Initializing small group...')
        if level0 is None:
            level0 = base.ideal(1)
        self.G0 = ArithGroup_nf_matrix(base, base(1), base(1), level0, grouptype=grouptype, magma=magma, timeout=timeout, compute_presentation=True)
        self._G0_gens_as_matrices = [self.G0.quaternion_to_matrix(g.quaternion_rep) for g in self.G0.gens()]
        verbose('Done initializing small level group.')
        self.F = base
        self.B = self.G0.B
        self.magma = magma
        self._grouptype = grouptype
        self.level = base.ideal(level)
        """
        Compute generators of the subgroup Gamma_0(N), where N is the specified level.

        Write down representatives of the cosets
        for Gamma_0(N) in Gamma(1), which we identify with P^1(O_F/N). We already have
        code to compute with this: namely, cusp_reduction_table does precisely this.

        ALGORITHM :

        Retrieve the cusp reduction table. Recall that this is a dictionary with keys
        given by tuples (a,c) representing the element (a:c) in P^1(O_F/N). The entries
        are C, A, where c is the corresponding cusp (from cusp_set) and A is a matrix 
        taking C to a matrix with bottom row (a:c).
        Generate the coset representatives: this is given by taking A*C as we range 
        over all (A,C) in the values of cusp_reduction_table
        coset_reps is now a dictionary: keys are elements of P^1(O_F/N), and values are
        matrices which are coset reps for Gamma_0(N) in Gamma(1) cor. to these elements.
        """
        verbose('Computing coset reps...')
        self._coset_reps = { key : set_immutable(a * c) for key, (a, c) in self.cusp_reduction_table()[0].items() }
        verbose('Done computing coset reps.')
        ## compute the generators of H
        verbose('Computing the auxiliar data...')
        self._gens_dict_auxiliary, self._gens_matrices_auxiliary, self._gens_words_auxiliary = self._generators_auxiliary()
        if len(self._gens_dict_auxiliary) == 0: # DEBUG line
            return # DEBUG line
        verbose('Done computing the auxiliary data.')
        verbose('Computing GAP information...')
        self._compute_gap_information()
        verbose('Done with GAP information...')
        ArithGroup_nf_generic.__init__(self, base, base(1), base(1),self.level,info_magma = None,grouptype =  grouptype,magma = magma,timeout = timeout, compute_presentation = False)

    def _repr_(self):
        return 'Gamma0(%s) over %s'%(self.level.gens_reduced()[0], self.F)

    def get_word_rep(self, x):
        wd_aux = self._get_word_rep_auxiliary(self.G0.quaternion_to_matrix(x))
        iso = self._iso_mapping
        ans = []
        for i in wd_aux:
            if i > 0:
                ans += iso[i-1]
            else:
                ans += [-o for o in list(reversed(iso[-i-1]))]
        return ans

    def embed(self, x):
        return self.quaternion_to_matrix(x).apply_map(self._F_to_local)

    def _compute_gap_information(self):
        gens = [o.quaternion_rep for o in self.G0.gens()]
        relation_words = self.G0.get_relation_words()
        new_generators = self._gens_words_auxiliary
        G1 = FreeGroup(len(gens)).quotient(relation_words).gap()
        G1gens = G1.GeneratorsOfGroup()
        H1 = G1.Subgroup([prod((G1gens[ZZ(i).abs() - 1]**ZZ(i).sign() for i in wd),G1gens[0]**0) for wd in new_generators])
        iso = H1.IsomorphismFpGroup()
        H2 = iso.Range()
        H2gens = H2.GeneratorsOfGroup()
        H2relators = H2.RelatorsOfFpGroup()
        # Parse generators of H2 into Sage
        H2genlen = len(H2gens)
        self._final_gens = []
        self.Ugens = []
        for idx, g in enumerate(H2gens):
            update_progress(float(idx+1) / float(H2genlen), 'Parsing generators of H2')
            wd = iso.PreImagesRepresentative(g).UnderlyingElement().LetterRepAssocWord().sage()
            self._final_gens.append(wd)
            self.Ugens.append(prod(gens[ZZ(i).abs() - 1]**ZZ(i).sign() for i in wd))
        self._gens = [ self.element_class(self,quaternion_rep = g, word_rep = [i+1],check = False) for i,g in enumerate(self.Ugens) ]



        H2relatorlen = len(H2relators)
        if H2relatorlen > 0:
            # Parse relators
            self._relation_words = []
            for idx, wd in enumerate(H2relators):
                update_progress(float(idx+1) / float(H2relatorlen), 'Parsing relators for H2')
                self._relation_words.append(wd.UnderlyingElement().LetterRepAssocWord().sage())

        # Calculate final_gens as matrices
        self._iso_mapping = []
        H1gens = H1.GeneratorsOfGroup()
        H1genlen = len(H1gens)
        for idx, g in enumerate(H1gens):
            update_progress(float(idx+1) / float(H1genlen), 'Parsing isomorphism')
            self._iso_mapping.append( iso.ImageElm(g).UnderlyingElement().LetterRepAssocWord().sage())
        return

    def _represent_in_coset(self,g, check=False):
        """
        g is an element of Gamma(1). Represent it as h * p, where h in Gamma_0 and p is a rep.
        """
        ## We can read off the class from the bottom row, computing in P(O_F/N)
        c, d = g.row(1)
        P = self.get_P1List()
        N = P.N()
        coset_class = P.normalize(c,d) if self.F == QQ else P.normalize(c,d).tuple()
        rep = self._coset_reps[coset_class]
        h = g * rep.adjugate()
        set_immutable(h)
        if check:
            ## Now check that h really is in Gamma_0(N)
            if self.F == QQ:
                assert h[1][0] % N == 0
            else:
                assert h[1][0] in N
        return h, rep

    @cached_method
    def _generators_auxiliary(self):
        """
        Compute generators for Gamma_0(N) via its right coset representatives in Gamma(1).

        OUTPUT:
            - small_gens_matrices, a dictionary: the keys are matrices A,
                which are generators of the small group, and the values are integers;

            - small_gens_words, a list: the D[A]-th entry is the matrix A written
                as a word in the generators of Gamma(1).

        The words are written in Tietze form, i.e. [1,2,1,-2,-1,2] corr. to
        g * h * g * h^(-1) * g^(-1) * h, where g,h = (ordered) gens of Gamma(1).

        """
        g0gens = self._G0_gens_as_matrices
        small_gens_matrices_dict = {} ## This will contain the output: matrix form, dictionary with keys the matrices
        small_gens_matrices = [] ## list of the matrices in order
        small_gens_words = [] ## This will contain the output: word form.
        current_index = 0

        ## Loop over all gens of big group
        total_iterations = len(2 * g0gens) * len(self._coset_reps.items())
        iteration = 0
        for g in g0gens + [~g for g in g0gens]:
            ## Loop over all coset reps
            for key, p in self._coset_reps.items():
                ## compute p*g, represent as h * p_prime for h in subgroup
                h, p_prime = self._represent_in_coset(p * g)
                ## check h is not 1 and not repeating gens or their inverses
                hinv = h.adjugate()
                set_immutable(hinv)
                set_immutable(h)
                iteration += 1
                update_progress(float(iteration) / float(total_iterations), "Computing auxiliary generators")
                if not h == 1 and not h in small_gens_matrices_dict and not hinv in small_gens_matrices_dict:
                    ## This is new. Add h to the dictionary and add one to the index for next time
                    small_gens_matrices_dict[h] = current_index
                    current_index += 1
                    ## also add h to the list of matrices
                    small_gens_matrices.append(h)
                    ## Now solve the word problem
                    word = self.G0.get_word_rep(self.G0.matrix_to_quaternion(h))
                    small_gens_words.append(word)
        return small_gens_matrices_dict, small_gens_matrices, small_gens_words

    def _get_word_rep_auxiliary(self,h, check=False):
        """
        Solve the word problem in the small group Gamma_0(N) in the list of generators output 
        by _generators_auxiliary.

        Firstly, we write this as h = 1.h. Then we write h = gh', where g in Gens(G) (so we must be
        able to solve the word problem for G). Then write 1.g = zp', so that
            h = z * p' * h'. Now iterate. We will end up with z_1 z_2 ... z_t p_0, where p_0 = id rep.

        OUTPUT:

        - a list of integers in {-t,-t+1,...,t-1,t}, where the output of _generators_auxiliary is
          [a_1,...,a_t].

        For example,

           h = abc in H, a,b,c in Gens(G)
           h = 1.abc
             = 1ap^(-1) . pbc
             = 1ap^(-1) . pbq^(-1) . qc
             = 1ap^(-1) . pbq^(-1) . qc1^(-1)
             = z1 . z2 . z3, where each zi is in the generating set.
        """
        gens_G = self._G0_gens_as_matrices

        ## Initialise final output
        h_level_N_wp = []

        ## Write h in the generators of g
        h_level0_wp = self.G0.get_word_rep(self.G0.matrix_to_quaternion(h))

        ## We start with p_0 = id representative
        current_p = matrix([[1,0],[0,1]])
        set_immutable(current_p)

        ## loop through every generator that appears in the word of h (in G)
        for gen_ind in h_level0_wp:
            ## Compute the generator we're processing
            current_gen = gens_G[ZZ(gen_ind).abs()-1]
            if ZZ(gen_ind).sign() == -1:
                current_gen = current_gen.adjugate()
            ## Compute the generator and update p_i to p_{i+1}
            h_current, current_p = self._represent_in_coset(current_p * current_gen)
            ## h_current should be one of our generators! As it is of form p'gp^(-1)
            if h_current != 1: ## check not identity
                try:
                    gen_number = self._gens_dict_auxiliary[h_current]
                    ## Great, we've found a generator. Let's move on
                    ## Compute the index corresponding to this generator
                    ## The generator appearing is not inverse. So append the index
                    h_level_N_wp.append(gen_number + 1)
                except KeyError:
                    ## h_current^(-1) should be in the dictionary
                    h_curr_inv = h_current.adjugate()
                    set_immutable(h_curr_inv)
                    ## Great, we've found a generator. Let's move on
                    ## Compute the index corresponding to this generator
                    gen_number = self._gens_dict_auxiliary[h_curr_inv]
                    ## The generator appearing is an inverse. So append negative the index
                    h_level_N_wp.append(-gen_number-1)

        ## Check that we have actually solved the word problem correctly
        if check:
            check_h = prod(self._gens_matrices_auxiliary[ZZ(i).abs() - 1]**(ZZ(i).sign()) for i in h_level_N_wp)
            assert check_h == h
        return h_level_N_wp

class ArithGroup_nf_matrix(ArithGroup_matrix_generic, ArithGroup_nf_kleinian):
    @cached_method
    def matrix_basis(self):
        F = self.F
        M = MatrixSpace(F,2,2)
        return [M([1,0,0,1]), M([1,0,0,-1]), M([0,-1,-1,0]), M([0,-1,1,0])]

    @cached_method
    def matrix_to_quaternion(self, x):
        F = self.B
        a, b, c, d = x.list()
        return self.B([(a+d) / 2, (a-d) / 2 , (-b - c) / 2, (c - b) / 2])

    @cached_method
    def quaternion_to_matrix(self, x):
        try:
            x = x.quaternion_rep
        except AttributeError: pass
        ans = sum((a * b for a, b in zip(list(self.B(x)), self.matrix_basis())))
        set_immutable(ans)
        return ans

    def _init_magma_objects(self,info_magma = None):
        wtime = walltime()
        verbose('Calling _init_magma_objects...')
        if info_magma is None:
            Qx_magma = self.magma.PolynomialRing(self.magma.Rationals())
            xm = Qx_magma.gen(1)
            f = self.F.gen().minpoly()
            fmagma = sum([self.magma(c)*xm**i for c,i in zip(f.coefficients(),f.exponents())])
            if f.degree() == 1:
                FF_magma = self.magma.RationalsAsNumberField()
            else:
                FF_magma = self.magma.NumberField(fmagma,DoLinearExtension = True)
            self._F_magma = FF_magma
            OF_magma = FF_magma.Integers()
            am, bm = sage_F_elt_to_magma(self._F_magma,self.a),sage_F_elt_to_magma(self._F_magma,self.b)
            self._B_magma = self.magma.QuaternionAlgebra(FF_magma,am,bm)
            i, j = self._B_magma.gen(1), self._B_magma.gen(2)
            k = i * j
            on = self._B_magma.One()
            self._Omax_magma = self.magma.Order([(on + i)/2, (j+k)/2, (j-k)/2, (on - i)/2])
            if self.level != self.F.ideal(1):
                levgen = sage_F_elt_to_magma(self._B_magma.BaseRing(), self.level.gens_reduced()[0])
                self._O_magma = self.magma.Order([(on + i)/2, -(j+k)/2, levgen * (k-j)/2, (on-i)/2])
                print self._O_magma.Discriminant().Norm()
            else:
                self._O_magma = self._Omax_magma
            if self._compute_presentation:
                self._D_magma = self.magma.UnitDisc(Precision = 300)
        else:
            self._F_magma = info_magma._F_magma
            OF_magma = info_magma._F_magma.Integers()
            self._B_magma = info_magma._B_magma
            self._Omax_magma = info_magma._Omax_magma
            if self.level != self.F.ideal(1):
                i, j = self._B_magma.gen(1), self._B_magma.gen(2)
                k = i * j
                Pgen = sage_F_elt_to_magma(self._F_magma, self.level.gens_reduced()[0])
                on = self._B_magma.One()
                self._O_magma = self.magma.Order([(on + i)/2, (j+k)/2,  Pgen * (j-k)/2, (on-i)/2])
            else:
                self._O_magma = self._Omax_magma
            if self._compute_presentation:
                self._D_magma = self.magma.UnitDisc(Precision = 300)
            else:
                try:
                    self._D_magma = info_magma._D_magma
                except AttributeError:
                    pass
        if not hasattr(self,'_F_magma'):
            self._F_magma = self._B_magma.BaseRing()
        verbose('Spent %s seconds in init_magma_objects'%walltime(wtime))

