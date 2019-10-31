######################
##                  ##
##    ARITHMETIC    ##
##    COHOMOLOGY    ##
##                  ##
######################
r'''

TESTS:

sage: from darmonpoints.findcurve import find_curve
sage: from darmonpoints.cohomology_abstract import *
sage: from darmonpoints.sarithgroup import *
sage: from darmonpoints.util import *
sage: from darmonpoints.cohomology_arithmetic import *
sage: F.<r> = QuadraticField(5)
sage: P = F.ideal(3/2*r + 1/2)
sage: D = F.ideal(3)
sage: abtuple = quaternion_algebra_invariants_from_ramification(F,D,F.real_places()[:1]) #  optional - magma
sage: G = BigArithGroup(P,abtuple, F.ideal(1), grouptype = 'PSL2',outfile = "/tmp/darmonpoints.tmp") #  optional - magma
sage: H = ArithCoh(G)           #  optional - magma
sage: primes = F.primes_of_degree_one_list(10) #  optional - magma
sage: H.hecke_matrix(primes[0]).charpoly() #  optional - magma
x^2 - 16
sage: ell = F.ideal(1/2*r + 5/2) #  optional - magma
sage: H.hecke_matrix(ell).charpoly() #  optional - magma
x^2 - 4
'''
from sage.structure.sage_object import SageObject
from sage.groups.group import AlgebraicGroup
from sage.structure.element import MultiplicativeGroupElement,ModuleElement
from sage.structure.parent import Parent
from sage.categories.homset import Hom
from sage.matrix.constructor import Matrix,matrix
from sage.misc.cachefunc import cached_method
from sage.structure.sage_object import load,save
from sage.misc.misc_c import prod
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,LaurentSeriesRing, Qp,Zp,Zmod,FiniteField
from collections import defaultdict
from itertools import product,chain,izip,groupby,islice,tee,starmap
from sage.rings.infinity import Infinity
from sage.arith.all import gcd, lcm, xgcd

from util import *
import os
from ocmodule import OCVn
from ocbianchi import BianchiDistributions, left_ps_adjuster
from sage.misc.persist import db, db_save
from sage.parallel.decorate import fork,parallel
from sage.matrix.constructor import block_matrix
from sage.rings.number_field.number_field import NumberField
from sage.categories.action import Action
import operator
from cohomology_abstract import *
from sage.matrix.matrix_space import MatrixSpace
from ocmodule import our_adjuster, ps_adjuster
from sage.modules.free_module_element import free_module_element, vector
from representations import *
from time import sleep
from sage.modular.pollack_stevens.padic_lseries import log_gamma_binomial
# from sage.modular.cusps import Cusp

def find_newans(Coh,glocs,ti):
    gens = Coh.group().gens()
    V = Coh.coefficient_module()
    try:
        N = len(V(0)._moments.list())
    except AttributeError:
        N = 1
    newans = [V.acting_matrix(glocs[0].matrix(), N).new_matrix() for u in gens]
    for gk0,tik in zip(glocs,ti):
        gk = V.acting_matrix(gk0.matrix(), N)
        fox_grad_k = Coh.fox_gradient(tik, red = lambda x:x.apply_map(lambda y: y % Coh._pN))
        for j,gj in enumerate(gens):
            newans[j] += gk * fox_grad_k[j]
            try:
                newans[j] = newans[j].apply_map(lambda x: x % Coh._pN)
            except PrecisionError:
                pass
    return newans

def get_overconvergent_class_matrices(p,E,prec, sign_at_infinity,use_ps_dists = False,use_sage_db = False,parallelize = False,progress_bar = False):
    # If the moments are pre-calculated, will load them. Otherwise, calculate and
    # save them to disk.
    if use_ps_dists == False:
        raise NotImplementedError, 'Must use distributions from Pollack-Stevens code in the split case'

    sgninfty = 'plus' if sign_at_infinity == 1 else 'minus'
    dist_type = 'ps' if use_ps_dists == True else 'fm'
    fname = 'moments_%s_%s_%s_%s_%s.sobj'%(p,E.cremona_label(),sgninfty,prec,dist_type)
    if use_sage_db:
        try:
            Phi = db(fname)
            return Phi
        except IOError: pass
    phi0 = E.pollack_stevens_modular_symbol()
    if sign_at_infinity == 1:
        phi0 = phi0.plus_part()
    elif sign_at_infinity == -1:
        phi0 = phi0.minus_part()
    else:
        assert sign_at_infinity == 0
        phi0 = phi0.plus_part() + phi0.minus_part()
    phi0 = 1 / gcd([val.moment(0) for val in phi0.values()]) * phi0
    verbose('Lifting..')
    Phi = phi0.lift(p,M = prec - 1,algorithm = 'greenberg',eigensymbol = True)
    verbose('Done lifting.')
    Phi._liftee = phi0
    return Phi

def get_overconvergent_class_quaternionic(P,phiE,G,prec,sign_at_infinity,sign_ap, use_ps_dists = False,use_sage_db = False,parallelize = False,progress_bar = False,method = None,Ename = 'unknown'):
    try:
        p = ZZ(P)
        Pnorm = p
        F = QQ
    except TypeError:
        p = ZZ(P.norm().factor()[0][0])
        Pnorm = ZZ(P.norm())
        F = P.number_field()

    if method is None:
        method = 'naive'
    else:
        if method != 'naive' and method != 'bigmatrix':
            raise ValueError('method should be either "naive" or "bigmatrix"')
    if Pnorm != p:
        raise NotImplementedError('For now I can only work over totally split')

    base_ring = Zp(p,prec)

    sgninfty = 'plus' if sign_at_infinity == 1 else 'minus'
    dist_type = 'ps' if use_ps_dists == True else 'fm'
    fname = 'moments_%s_%s_%s_%s_%s.sobj'%(p,Ename,sgninfty,prec,dist_type)
    if use_sage_db:
        try:
            Phivals = db(fname)
            CohOC = ArithCohOverconvergent(G,base = base_ring,use_ps_dists = use_ps_dists)
            CohOC._coeff_module = Phivals[0].parent()
            VOC = CohOC.coefficient_module()
            Phi = CohOC([VOC(o) for o in Phivals])
            return Phi
        except IOError: pass
    verbose('Computing moments...')
    CohOC = ArithCohOverconvergent(G,base = base_ring,use_ps_dists = use_ps_dists)
    Phi0 = CohOC(phiE)
    verbose('Now lifting...')
    Phi = CohOC.improve(Phi0, prec = prec,sign = sign_ap, parallelize = parallelize,progress_bar = progress_bar,method = method)
    if use_sage_db:
        raise NotImplementedError
        # db_save(Phi._val,fname)
    verbose('Done.')
    Phi.set_liftee(phiE)
    Phi._sign_ap = sign_ap
    return Phi

def get_overconvergent_class_bianchi(P,phiE,G,prec, aP, aPbar, sign_at_infinity,sign_ap, parallelize = False, progress_bar = False,method = None,Ename = 'unknown'):
    if parallelize:
        raise NotImplementedError
    p = ZZ(P.norm().factor()[0][0])
    Pnorm = ZZ(P.norm())
    F = P.number_field()
    pOF = [o for o, _ in F.ideal(p).factor()]
    Pbar = pOF[0] if P == pOF[1] else pOF[1]
    assert P * Pbar == F.ideal(p)

    self._aP = aP
    self._aPbar = aPbar

    if method is None:
        method = 'naive'
    else:
        if method != 'naive' and method != 'bigmatrix':
            raise ValueError('method should be either "naive" or "bigmatrix"')
    if Pnorm != p:
        raise NotImplementedError('For now I can only work over totally split')

    base_ring = Zp(p,prec)
    if sign_at_infinity == 0:
        sgninfty = 'zero'
    elif sign_at_infinity == 1:
        sgninfty = 'plus'
    elif sign_at_infinity == -1:
        sgninfty = 'minus'
    else:
        raise ValueError("sign_at_infinity (= %s) should be one of -1, 0, 1"%sign_at_infinity)

    verbose('Computing moments...')
    CohOC = ArithCohBianchi(G,base = base_ring)
    Phi0 = CohOC(phiE)
    pi, pi_bar = [o.gens_reduced()[0] for o, _ in G.F.ideal(G.prime()).factor()]
    if F.ideal(pi) != G.ideal_p:
        pi, pi_bar = pi_bar, pi
    assert F.ideal(pi) == G.ideal_p
    CohOC.P_gen = pi
    CohOC.Pbar_gen = pi_bar
    verbose('Now lifting...')
    Phi = CohOC.improve(Phi0, prec = prec,sign = sign_ap, parallelize = parallelize,progress_bar = progress_bar,method = method)
    verbose('Done.')
    Phi.set_liftee(phiE)
    Phi._sign_ap = sign_ap
    return Phi

class ArithCohElement(CohomologyElement):
    r"""
    Class for working with arithmetic cohomology elements. In particular,
    can handle elements of H^1(G,D), where G = congruence subgroup and D
    is a module of distributions.

    The coefficient module (e.g. D) is self.parent().coefficient_module().

    Initialised by giving the parent arithmetic cohomology group - an ArithCoh
    object - and %data%.

    This should work equally well for classical and Bianchi modular forms.
    This choice is encoded (and hard-coded) in the ArithCoh parent class:
    in particular, it determines the choice of distribution modules used,
    e.g. either 1- or 2-variable distributions.
    """
    def __init__(self, parent, data):
        ## dictionary of coefficients of the p-adic L-series
        self._Lseries_coefficients = {}
        super(ArithCohElement,self).__init__(parent, data)

    def set_liftee(self,x):
        self._liftee = x

    def get_liftee(self):
        return self._liftee

    def _repr_(self):
        return 'Arithmetic cohomology class in %s'%self.parent()

    def Tq_eigenvalue(self, ell, check = True):
        r"""
        Computes the eigenvalue of the T_q operator (where q = ell in the input)
        acting on the cohomology class self. 

        Warning: assumes that self IS a Hecke eigenclass, and that the eigenvalue
        thus exists.
        """
        # Assume that self IS a hecke eigenclass
        if hasattr(self, 'elliptic_curve'):
            return self.elliptic_curve.ap(ell)
        try:
            f0 = self.get_liftee()
        except AttributeError:
            f0 = self
        if not f0.parent().trivial_action():
            raise NotImplementedError
        f = f0.parent().apply_hecke_operator(f0, ell)
        ans = ZZ(f / f0)
        if check:
            assert (ans * f0).values() == f.values()
        return ans

    def evaluate_cuspidal_modsym_at_cusp_list(self, cusp_list,j = None, q = None):
        r"""
        Takes arithmetic cohomology class Phi (=self) in H^1(G,D) and evaluates it at a list of
        cusp (cusp_list). Fundamentally calls the function evaluate_at_cusp_list, which inverts
        the natural map delta from modular symbols to arithmetic cohomology.

        The key functionality of this particular function is a toggle for killing Eisenstein
        contributions: the lift of self to a modular symbol need not be a cuspidal eigensymbol,
        since it can be polluted by anything in the kernel of delta. Since this kernel is
        Eisenstein, it is killed by T_q - N(q) - 1 for suitable primes q in the underlying field.

        Input:
            - cusp list: list of cusps with coefficients. Represented as pairs (n,(a,c)),
                where n is the coefficient and (a,c) represents the cusp a/c.

            - j  : if specified, returns the jth moment of the resulting distribution.
                   if not, returns the whole distribution. Can be int (classical) or tuple (Bianchi).

            - q (int) : auxiliary prime used to kill Eisenstein contributions. If set to
                -1, ignores this completely. If not, computes a prime q and applies
                T_q - q - 1 to recover a cuspidal eigensymbol by killing Eisenstein part.

        Output:
            either a distribution (if j = None) or the jth moment of this distribution (else).
        """
        V = self.parent().coefficient_module() ## Working in H^1(G,V)
        K = V.base_ring() ## p-adic ring
        p = K.prime() ## underlying prime
        G = self.parent().group() ## arithmetic group Gamma
        N = G.level ## level of Gamma
        x = ZZ['x'].gen()

        ## If we are killing the Eisenstein part, compute a suitable prime to use
        if q is None:
            q = ZZ(1)
            while (N * p) % q == 0:
                q = q.next_prime()

        ## If we are killing the Eisenstein part, then apply T_q - q - 1 to kill it
        scale = 1
        if q != -1:
            ## rescale by 1/(a_q - q - 1) so this operator is a projector to the cuspidal part 
            scale = (self.Tq_eigenvalue(q) - q - 1)**-1
            ans = self.parent().coefficient_module()(0)
            ## Loop over all the matrices g in T_q, and for each g generate a new cusp list from this
            for g in G.get_hecke_reps(q):
                g_inv = M2Z(g.adjugate())
                new_cusp_list = []
                a, b, c, d = g_inv.list()
                for n, cc in cusp_list:
                    new_cusp_list.append((n, (a * cc[0] + b * cc[1], c * cc[0] + d * cc[1])))
                ## Evaluate at this new list of cusps, and then hit the output - a distribution - with the Hecke matrix g
                ans += g * self.evaluate_at_cusp_list(new_cusp_list)#[(n, cc.apply(g_inv.list())) for n, cc in cusp_list]
            ans -= (q+1) * self.evaluate_at_cusp_list(cusp_list)
        else:
            ## We're *not* killing the Eisenstein part. Just evaluate at the cusps here
            ans = self.evaluate_at_cusp_list(cusp_list)

        ## Return either whole distribution or just jth moment, depending on input
        if j is None:
            return ans._rmul_(scale)
        else:
            return scale * ans.evaluate_at_poly(x**j)

    @cached_method
    def cusp_boundary_element(self, cusp):
        r"""
        Function to explicitly realise a parabolic arithmetic cohomology class
        as a coboundary after restriction to the stabiliser of a cusp. This should
        work for any coefficient module on which the action of Sigma_0(p) is encoded
        in linear algebra.

        Input is a specific choice of cusp, as a tuple (a,c), representing a/c in P^1(F).
        Then computes the stabiliser of this cusp inside the group G=Gamma. We assume that
        self is in the kernel of restriction to this cusp, which will be the case
        for any lift of a cuspidal class to overconvergent coefficients. Then we
        set up a linear algebra problem to compute an element v in V such that
            self(gamma) = v|gamma^-1 - v
        for all gamma in Stab_G(a/c).

        Returns this v.
        """
        H = self.parent() ## Cohomology group
        V = H.coefficient_module() ## Coefficient module in H^1(G,V)
        K = V.base_ring() ## p-adic ring
        prec = K.precision_cap()
        G = H.group() ## Gamma
        a, c = cusp 

        ## Find element of SL2 representing this cusp
        try: ## if we're working over QQ
            g, d, b = a.xgcd(-c)
        except AttributeError: ## xgcd doesn't work over F != QQ; compute directly in this case
            if a.gcd(c) != 1:
                raise ValueError('a, c not coprime.')
            F = G.base_field().ring_of_integers()
            ideal_c = F.ideal(c)
            d = next(x for x in ideal_c.residues() if a * x - 1 in ideal_c)
            b = (1 - a * x) / c
        assert a * d - b * c == 1 ## Check we really are in SL2

        gamma = Matrix([[a,b],[c,d]]) ## gamma represents cusp a/c

        ## Compute generators of a finite index subgroup of the stabiliser of gamma in G.
        ## Tlist will be a list of matrices in this stabiliser.
        Tlist = G.compute_cusp_stabiliser(gamma) 

        ## Now set up our linear system Av = b; A is a stack of the matrices in Tlist acting
        ## on the coefficients V, and b is a stack of the vectors corr. to values of self at Tlist
        A = V.acting_matrix(Tlist[0], prec + 1).change_ring(K) - 1 ## Initialise at first elt of Tlist
        b = self.evaluate(Tlist[0])._val ## Initialise at first elt of Tlist
        for T in Tlist[1:]: ## Create rest of stack
            A = A.stack(V.acting_matrix(T, prec + 1).change_ring(K) - 1)
            b = b.stack(self.evaluate(T)._val)
        ## Solve for v. check=False makes computation work even with varying precision in Zp
        ans = V(A.solve_right(b, check=False)) 
        return ans

    def evaluate_at_cusp_list(self, cusp_list):
        """
        Our cohomology class, in H^1(G,V), is the image of a modular symbol Phi in Symb_G(V)under the natural 
        connecting map in cohomology. This function computes the value Phi(D), where D is a divisor. 

        D is represented by input cusp_list, which is a list of pairs (n,cusp), where n is the coefficient
        (an integer) and cusp is a tuple (a,c) representing a/c; e.g. [(1,(3,4)),(-2,(1,0))] gives 
            D = [3/4] - 2[inf].

        Returns the value Phi(D) as an element of V.
        """
        symb = 0
        ## Run over all cusps in the divisor one by one
        for n, cusp in cusp_list:
            gamma, A = self.parent().group().find_matrix_from_cusp(cusp)
            ## Use formula for inversion of connecting map: for formula, see paper 'Explicit Bianchi p-adic...'
            symb += n * (gamma**-1 * (self.evaluate(gamma) + self.cusp_boundary_element((A[0,0],A[1,0]))))
        return symb

    @cached_method
    def BI(self, h, j = None): # Returns \int_{h \Z_p} z^j \Phi\{0 \to \infy\}
        r"""
        BI = 'Basic Integral'. Computes the basic integrals required in the computation
        of the p-adic L-function.

        Input a 2x2 matrix h in SL2(OK) (which embeds as an element of Sigma_0(p)), and a value j.
        
        Options for j:
            - classical case: specify a non-negative integer j. Then returns the value 
                    BI_{h,j} := Int_{h.Zp} z^j . d Phi{0 --> infty},
                that is, the value of the distribution Phi{0 --> infty} at the function z^j x 
                the indicator function of the open set h.Zp. 

            - Bianchi case: specify a tuple (k,l). Then returns the value 
                    BI_{h,j} := Int_{h.(Zp x Zp)} x^k y^l . d Phi{0 --> infty},
                that is, the value of the distribution Phi{0 --> infty} at the function x^k y^l x 
                the indicator function of the open set h.(Zp x Zp). 

            - do not specify j. Then returns the the distribution mu whose moments are
                BI_{h,j}. 

        """
        V = self.parent().coefficient_module() ## Module V in H^1(G,V)
        p = V.base_ring().prime() ## base ring is p-adics, p underlying prime
        x = ZZ['x'].gen()
        scale = ZZ(self.Tq_eigenvalue(p))**-1 ## U_p eigenvalue

        ## make cusp_list corresponding to {h.0 --> h.inf} = [h.inf] - [h.0]
        cusp_list = [(1, (h[0,1],h[0,0])), (-1, (h[1,1],h[1,0]))]
        symb = self.evaluate_cuspidal_modsym_at_cusp_list(cusp_list)

        ## now act on result by h: put h into Sigma0 (or Sigma0^2, Bianchi case), then apply h^-1 on left
        a,b,c,d = h.list()
        g = V.Sigma0()(Matrix(ZZ,2,2,[-a,b,-c,d]))
        ans = (g * symb)._rmul_(scale)

        ## Check if we're returning the whole distribution or just the jth moment, then return
        if j is None:
            return ans
        else:
            return ans.moment(j)

    def get_Lseries_term(self, n, cov = None):
        r"""
        Return the `n`-th coefficient of the `p`-adic `L`-series attached to an
        element of H^1(G,D).

        Currently hard-coded rational: need to update for Bianchi too.
        """
        ## Perhaps we've already computed this. If we have, then return it
        if n in self._Lseries_coefficients:
            return self._Lseries_coefficients[n]
        else:
            ## We need to compute this for the first time
            G = self.parent().S_arithgroup() ## G = Gamma
            p = G.prime() ## underlying prime
            ap = self._sign_ap

            ## Specify a topological generator of 1 + pZp
            if p == 2:
                gamma = 1 + 4
            else:
                gamma = 1 + p

            K = self.parent().coefficient_module().base_ring() ## p-adic ring
            precision = K.precision_cap()

            ## Initialise power series ring, where output will be valued
            S = K[['z']]
            z = S.gen()
            M = precision
            if n == 0:
                precision = M
                lb = [1] + [0 for a in range(M - 1)]
            else:
                lb = log_gamma_binomial(p, gamma, n, 2 * M)
                if precision is None:
                    precision = min([j + lb[j].valuation(p)
                                     for j in range(M, len(lb))])
                lb = [lb[a] for a in range(M)]

            if cov is None:
                cov = G.get_Up_reps()[1:]
                ## BIANCHI CASE: TO BE CHANGED
                ## Recall our fixed choice of uniformisers
                #pi,pibar = self.parent().P_gen,self.parent().Pbar_gen
                ## G.get_Up_reps_Bianchi(pi,pibar)....
            dn = 0
            for h in cov:
                aa = K.teichmuller(h[0,1] / h[1,1])
                f = sum(lj * (1/aa * z - 1)**j for j, lj in enumerate(lb))
                dn += self.BI(h, None).evaluate_at_poly(f)
            self._Lseries_coefficients[n] = dn.add_bigoh(precision)
            return self._Lseries_coefficients[n]


class ArithCoh_generic(CohomologyGroup):
    r"""
    Class for computing with arithmetic cohomology groups.

    Parent class for ArithCohElement.

    Initialised by inputting an arithmetic group G, and options for
    using overconvergent coefficients over a base ring, and whether
    or not to use Pollack-Stevens distributions.
    """
    Element = ArithCohElement
    def __init__(self,G,base = None,use_ps_dists = False):
        self._S_arithgroup = G
        self._use_ps_dists = use_ps_dists
        self._use_shapiro = G._use_shapiro
        if self._use_shapiro:
            CohomologyGroup.__init__(self, G.large_group(), CoIndModule(G,V,trivial_action = trivial_action), False)
        else:
            CohomologyGroup.__init__(self, G.small_group(), V, trivial_action)

    def use_shapiro(self):
        return self._use_shapiro

    def S_arithgroup(self):
        return self._S_arithgroup

    def _element_constructor_(self,data):
        raise NotImplementedError

    @cached_method
    def hecke_matrix(self, l, use_magma = True, g0 = None): # l can be oo
        dim = self.dimension()
        R = self.coefficient_module().base_ring()
        M = matrix(R,dim,dim,0)
        for j,cocycle in enumerate(self.gens()):
            # Construct column j of the matrix
            verbose('Constructing column %s/%s of the matrix'%(j,dim))
            fvals = self.apply_hecke_operator(cocycle, l, use_magma = use_magma, g0 = g0)
            M.set_column(j,list(vector(fvals)))
        return M

    def Up_matrix(self):
        dim = self.dimension()
        R = self.coefficient_module().base_ring()
        M = matrix(R,dim,dim,0)
        for j,cocycle in enumerate(self.gens()):
            # Construct column j of the matrix
            fvals = self.apply_Up(cocycle)
            M.set_column(j,list(vector(fvals)))
        return M

    def apply_hecke_operator(self,c,l, hecke_reps = None,group = None,scale = 1,use_magma = True,g0 = None):
        r"""

        Apply the l-th Hecke operator operator to ``c``.

        """
        # verbose('Entering apply_hecke_operator')
        if hecke_reps is None:
            hecke_reps = self.group().get_hecke_reps(l,use_magma = use_magma, g0 = g0)
        # verbose('Got hecke reps')
        V = self.coefficient_module()
        padic = not V.base_ring().is_exact()
        group = self.group()
        if padic:
            prec = V.base_ring().precision_cap()
        else:
            prec = None
        vals = []
        R = V.base_ring()
        gammas = group.gens()
        vals = [V(0) for gamma in gammas]
        input_vector = []
        # verbose('Calculating action')
        for j, gamma in enumerate(gammas):
            # verbose('generator %s/%s...'%(j+1,len(gammas)))
            for g in hecke_reps:
                if self.trivial_action():
                    vals[j] += c.evaluate(group.get_hecke_ti(g,gamma,l,use_magma, reps = hecke_reps))
                else:
                    vals[j] += g * c.evaluate(group.get_hecke_ti(g,gamma,l,use_magma, reps = hecke_reps))
        return scale * self(vals)

class ArithAction(Action):
    r'''
    Encodes de action of an arithmetic group on the distributions module
    '''
    def __init__(self,G,M, act=None):
        if act is None:
            self._act = lambda g, v: v.parent().Sigma0()(g) * v
        else:
            self._act = act
        Action.__init__(self,G,M,is_left = True,op = operator.mul)

    def _act_(self,g,v):
        return self._act(g, v)

class BianchiArithAction(Action):
    r'''
    Encodes de action of an arithmetic group on the distributions module
    '''
    def __init__(self,G,M):
        Action.__init__(self,G,M,is_left = True,op = operator.mul)

    def _act_(self,g,v):
        V = v.parent()
        prec = V.precision_cap()
        qrep = g.parent().matrix_rep(g) # This method is only available for matrix ring (not quaternionic)
        qrep_bar = qrep.apply_map(lambda x:x.trace() - x)
        first, second = g.parent().embed_matrix(qrep, prec), g.parent().embed_matrix(qrep_bar, prec)
        return V.Sigma0Squared()(first,second) * v

class CohArbitrary(CohomologyGroup):
    Element = CohomologyElement
    def __init__(self, G, V, action_map=None):
        self._V = V
        self._G = G
        if action_map is not None:
            action = ArithAction(G, V, action_map)
            V._unset_coercions_used()
            V.register_action(action)
        CohomologyGroup.__init__(self, self._G, self._V, False)

    def group(self):
        return self._G

    def coefficient_module(self):
        return self._V

    def get_hecke_data(self, ell, hecke_reps = None, use_magma= True, g0=None):
        group = self.group()
        if hecke_reps is None:
            hecke_reps = group.get_hecke_reps(ell, use_magma = use_magma, g0 = g0)
        hecke_data = {}
        for gamma in group.gens():
            for g in hecke_reps:
                set_immutable(g)
                ti = group.get_hecke_ti(g,gamma,ell,use_magma, reps = hecke_reps)
                set_immutable(ti)
                hecke_data[(g, gamma.quaternion_rep)] = ti
        return hecke_data

    def apply_hecke_operator(self,c,l, hecke_reps = None,scale = 1,use_magma = True,g0 = None, as_Up = False, hecke_data = None):
        r"""
        Apply the l-th Hecke operator operator to ``c``.
        """
        group = self.group()
        if hecke_reps is None:
            hecke_reps = group.get_hecke_reps(l,use_magma = use_magma, g0 = g0)
        if as_Up:
            l = None
        if hecke_data is None:
            hecke_data = self.get_hecke_data(l, hecke_reps, use_magma=use_magma, g0=g0)
        vals = [sum(c.evaluate(hecke_data[(g, gamma.quaternion_rep)]).left_act_by_matrix(group(g).matrix()) for g in hecke_reps) for gamma in group.gens()] # DEBUG: g need not be in group...
        return scale * self(vals)


##=================================================================================

class ArithCohOverconvergent(ArithCoh_generic):
    def __init__(self, G, base, use_ps_dists = False):
        trivial_action = False
        self._overconvergent = 1
        if self._use_ps_dists:
            from sage.modular.pollack_stevens.distributions import OverconvergentDistributions
            V = OverconvergentDistributions(0,base = base, prec_cap = base.precision_cap(), act_on_left = True,adjuster = our_adjuster(), dettwist = 0) # Darmon convention
            V.Sigma0 = lambda :V._act._Sigma0
        else:
            V = OCVn(base.prime(), 1 + base.precision_cap())
        arith_act = ArithAction(G.small_group(), V)
        V._unset_coercions_used()
        V.register_action( arith_act )
        self._pN = V._p**base.precision_cap()

    def _element_constructor_(self,data):
        if isinstance(data,list):
            V = self.coefficient_module()
            return self.element_class(self, [V(o) for o in data])
        elif isinstance(data,self.element_class):
            G = self.group()
            V = self.coefficient_module()
            prec = V.base_ring().precision_cap()
            try:
                data = data.get_liftee()
            except AttributeError:
                pass
            try:
                vals = [V(data.evaluate(g).moment(0), normalize=False).lift(M=prec) for g in G.gens()]
            except (AttributeError, TypeError):
                try:
                    vals = [V(data.evaluate(g), normalize=False).lift(M=prec) for g in G.gens()]
                except (AttributeError, TypeError):
                    vals = [V(data.evaluate(g)) for g in G.gens()]
            return self.element_class(self, vals)
        else:
            G = self.group()
            V = self.coefficient_module()
            return self.element_class(self, [V(data) for g in G.gens()])

    def get_Up_reps_local(self,prec):
        Up_reps = self.S_arithgroup().get_Up_reps()
        if prec is None:
            return Up_reps
        V = self.coefficient_module()
        try:
            V = V.coefficient_module()
        except AttributeError:
            pass
        S0 = V.Sigma0()
        return [S0(self.group().embed(g,prec), check = False) for g in Up_reps]

    def apply_Up(self,c,group = None,scale = 1,parallelize = False,times = 0,progress_bar = False,method = 'naive', repslocal = None, Up_reps = None, steps = 1):
        r"""
        Apply the Up Hecke operator operator to ``c``.
        """
        assert steps >= 1

        V = self.coefficient_module()
        R = V.base_ring()
        gammas = self.group().gens()

        if Up_reps is None:
            Up_reps = self.S_arithgroup().get_Up_reps()

        if repslocal is None:
            try:
                prec = V.base_ring().precision_cap()
            except AttributeError:
                prec = None
            repslocal = self.get_Up_reps_local(prec)
        i = 0
        if method == 'naive':
            assert times == 0
            G = self.S_arithgroup()
            Gn = G.large_group()
            if self.use_shapiro():
                if self.coefficient_module().trivial_action():
                    def calculate_Up_contribution(lst, c, i, j):
                        return sum([c.evaluate_and_identity(tt) for sk, tt in lst])
                else:
                    def calculate_Up_contribution(lst, c, i, j):
                        return sum([sk * c.evaluate_and_identity(tt) for sk, tt in lst])

                input_vec = []
                for j, gamma in enumerate(gammas):
                    for i, xi in enumerate(G.coset_reps()):
                        delta = Gn(G.get_coset_ti(set_immutable(xi * gamma.quaternion_rep))[0])
                        input_vec.append(([(sk, Gn.get_hecke_ti(g,delta)) for sk, g in zip(repslocal, Up_reps)], c, i, j))
                vals = [[V.coefficient_module()(0,normalize=False) for xi in G.coset_reps()] for gamma in gammas]
                if parallelize:
                    for inp, outp in parallel(calculate_Up_contribution)(input_vec):
                        vals[inp[0][-1]][inp[0][-2]] += outp
                else:
                    for inp in input_vec:
                        outp = calculate_Up_contribution(*inp)
                        vals[inp[-1]][inp[-2]] += outp
                ans = self([V(o) for o in vals])
            else:
                Gpn = G.small_group()
                if self.trivial_action():
                    def calculate_Up_contribution(lst,c,num_gamma):
                        return sum([c.evaluate(tt) for sk, tt in lst], V(0,normalize=False))
                else:
                    def calculate_Up_contribution(lst,c,num_gamma,pb_fraction=None):
                        i = num_gamma * len(lst)
                        verbose('pb_fraction = %s'%pb_fraction)
                        ans = V(0, normalize=False)
                        for sk, tt in lst:
                            ans += sk * c.evaluate(tt)
                            update_progress(i * pb_fraction, 'Up action')
                            i += 1
                        return ans
                input_vec = []
                for j,gamma in enumerate(gammas):
                    input_vec.append(([(sk, Gpn.get_hecke_ti(g,gamma)) for sk, g in zip(repslocal, Up_reps)], c, j))
                vals = [V(0,normalize=False) for gamma in gammas]
                if parallelize:
                    for inp,outp in parallel(calculate_Up_contribution)(input_vec):
                        vals[inp[0][-1]] += outp
                else:
                    for counter, inp in enumerate(input_vec):
                        outp = calculate_Up_contribution(*inp, pb_fraction=float(1)/float(len(repslocal) * len(input_vec)))
                        vals[inp[-1]] += outp
                ans = self(vals)
            if scale != 1:
                ans = scale * ans
        else:
            assert method == 'bigmatrix'
            verbose('Getting Up matrices...')
            try:
                N = len(V(0)._moments.list())
            except AttributeError:
                N = 1
            nreps = len(Up_reps)
            ngens = len(self.group().gens())
            NN = ngens * N
            A = Matrix(ZZ,NN,NN,0)
            total_counter = ngens**2
            counter = 0
            iS = 0
            for i,gi in enumerate(self.group().gens()):
                ti = [tuple(self.group().get_hecke_ti(sk,gi).word_rep) for sk in Up_reps]
                jS = 0
                for ans in find_newans(self,repslocal,ti):
                    A.set_block(iS,jS,ans)
                    jS += N
                    if progress_bar:
                        counter +=1
                        update_progress(float(counter)/float(total_counter),'Up matrix')
                iS += N
            verbose('Computing 2^(%s)-th power of a %s x %s matrix'%(times,A.nrows(),A.ncols()))
            for i in range(times):
                A = A**2
                if N != 0:
                    A = A.apply_map(lambda x: x % self._pN)
                update_progress(float(i+1)/float(times),'Exponentiating matrix')
            verbose('Done computing 2^(%s)-th power'%times)
            if times > 0:
                scale_factor = ZZ(scale).powermod(2**times,self._pN)
            else:
                scale_factor = ZZ(scale)
            bvec = Matrix(R,NN,1,[o for b in c._val for o in b._moments.list()])
            if scale_factor != 1:
                bvec = scale_factor * bvec
            valmat = A * bvec
            appr_module = V.approx_module(N)
            ans = self([V(appr_module(valmat.submatrix(row=i,nrows = N).list())) for i in xrange(0,valmat.nrows(),N)])
        if steps <= 1:
            return ans
        else:
            return self.apply_Up(ans, group = group,scale = scale,parallelize = parallelize,times = times,progress_bar = progress_bar,method = method, repslocal = repslocal, steps = steps -1)

    def improve(self, Phi, prec = None, sign = None, parallelize = False,progress_bar = False,method = 'naive', steps = 1):
        r"""

        Repeatedly applies U_p. Used in lifting theorems: 'improves' the precision of
        an overconvergent lift.

        (Applies Greenberg's lifting idea; see his paper in Israel J. Math.)

        """
        U = self.coefficient_module()
        group = self.group()
        if prec is None:
            prec = U.base_ring().precision_cap()
        assert prec is not None
        repslocal = self.get_Up_reps_local(prec)
        if method == 'naive':
            h2 = self.apply_Up(Phi, group = group, scale = 1,parallelize = parallelize,times = 0,progress_bar = False,method = 'naive', steps = steps)
            if progress_bar:
                update_progress(float(0)/float(prec),'f|Up')
            else:
                verbose('Applied Up once')

            h2 = self.apply_Up(h2, group = group, scale = 1,parallelize = parallelize,times = 0,progress_bar = False,method = 'naive', steps = steps)
            ii = 0
            try:
                current_val = min([(u-v).valuation() for u,v in zip([o for w in h2.values() for o in w.values()],[o for w in Phi.values() for o in w.values()])])
            except AttributeError:
                current_val = min([(u-v).valuation() for u,v in zip(h2.values(),Phi.values())])
            if progress_bar:
                update_progress(float(current_val)/float(prec),'f|Up')
            else:
                verbose("Applied Up twice")
            old_val = current_val - 1
            while current_val < prec and current_val > old_val:
                h1 = h2
                old_val = current_val
                ii += 2
                h2 = self.apply_Up(h1, group = group, scale = 1,parallelize = parallelize,times = 0,progress_bar = False,method = 'naive', steps = steps)
                if progress_bar:
                    update_progress(float(current_val)/float(prec),'f|Up')
                else:
                    verbose('Applied Up %s times (val = %s)'%(ii+1,current_val))
                h2 = self.apply_Up(h2, group = group, scale = 1,parallelize = parallelize,times = 0,progress_bar = False,method = 'naive', steps = steps)
                try:
                    current_val = min([(u-v).valuation() for u,v in zip([o for w in h2.values() for o in w.values()],[o for w in h1.values() for o in w.values()])])
                except AttributeError:
                    current_val = min([(u-v).valuation() for u,v in zip(h2.values(),h1.values())])
                if ii == 2 and current_val <= old_val:
                    raise RuntimeError("Not converging, maybe ap sign is wrong?")
                if progress_bar and ii + 1 <= prec:
                    update_progress(float(current_val)/float(prec),'f|Up')
                else:
                    verbose('Applied Up %s times (val = %s)'%(ii+2,current_val))
            Phi._val = h2._val
            if progress_bar and current_val < 1:
                update_progress(float(1.0),'f|Up')
            return h2
        else:
            assert method == 'bigmatrix'
            return self.apply_Up(Phi, group = group, scale = 1, parallelize = parallelize,times = len(ZZ(prec-1).bits()),progress_bar = progress_bar,method = 'bigmatrix',repslocal = repslocal, steps = steps)

class ArithCohBianchi(ArithCoh_generic):
    def __init__(self, G, base, use_ps_dists = False):
        self._overconvergent = 2
        trivial_action = False
        V = BianchiDistributions(base.prime(), 1 + base.precision_cap(), act_on_left=True, adjuster=left_ps_adjuster())
        arith_act = BianchiArithAction(G.small_group(), V)
        V._unset_coercions_used()
        V.register_action( arith_act )
        self.P_gen = None
        self.Pbar_gen = None
        self._pN = V._p**base.precision_cap()

    def _element_constructor_(self,data):
        if isinstance(data,list):
            V = self.coefficient_module()
            return self.element_class(self, [V(o) for o in data])
        elif isinstance(data,self.element_class):
            G = self.group()
            V = self.coefficient_module()
            prec = V.base_ring().precision_cap()
            try:
                data = data.get_liftee()
            except AttributeError:
                pass
            try:
                vals = [V(data.evaluate(g).moment(0), normalize=False).lift(M=prec) for g in G.gens()]
            except (AttributeError, TypeError):
                try:
                    vals = [V(data.evaluate(g), normalize=False).lift(M=prec) for g in G.gens()]
                except (AttributeError, TypeError):
                    vals = [V(data.evaluate(g)) for g in G.gens()]
            return self.element_class(self, vals)
        else:
            G = self.group()
            V = self.coefficient_module()
            return self.element_class(self, [V(data) for g in G.gens()])

    @cached_method
    def get_Up_reps_local(self,prec, pi, pi_bar):
        Up_reps, Up_reps_bar = self.S_arithgroup().get_Up_reps_bianchi(pi, pi_bar)
        phi = lambda x: self.group().matrix_rep(x)
        emb = self.group().embed
        if prec is None:
            return Up_reps, Up_reps_bar
        V = self.coefficient_module()
        try:
            V = V.coefficient_module()
        except AttributeError:
            pass
        S0 = V.Sigma0Squared()
        ans0 = []
        ans1 = []
        conj = lambda m : m.parent()([o.trace() - o for o in list(m)])
        for g in Up_reps:
            ans0.append(S0(emb(g,prec), emb(conj(g),prec)))
        for gbar in Up_reps_bar:
            ans1.append(S0(emb(gbar,prec), emb(conj(gbar),prec)))
        return ans0, ans1

    def apply_Up(self,c,group = None,scale = 1,progress_bar = False):
        V = self.coefficient_module()
        R = V.base_ring()
        gammas = self.group().gens()
        pi, pi_bar = self.P_gen, self.Pbar_gen

        Up_reps, Up_reps_bar = self.S_arithgroup().get_Up_reps_bianchi(pi, pi_bar)

        try:
            prec = V.base_ring().precision_cap()
        except AttributeError:
            prec = None
        repslocal, repslocal_bar = self.get_Up_reps_local(prec, pi, pi_bar)

        G = self.S_arithgroup()
        Gn = G.large_group()
        Gpn = G.small_group()
        i = 0
        input_vec = []
        for j,gamma in enumerate(gammas):
            input_vec.append(([(sk, Gpn.get_hecke_ti(g,gamma,reps = tuple(Up_reps))) for sk, g in zip(repslocal, Up_reps)], c, j))

        vals = [V(0,normalize=False) for gamma in gammas]
        pb_fraction = QQ(1) / (2 * len(repslocal) * len(input_vec))
        progress = 0
        for lst, c, j in input_vec:
            outp = V(0, normalize=False)
            for sk, tt in lst:
                progress += pb_fraction
                outp += sk * c.evaluate(tt)
                update_progress(float(progress), 'Up action (%s)'%(2 * len(repslocal) * len(input_vec)))
            vals[j] += outp
        ans = self(vals)
        c = ans
        input_vec = []
        for j,gamma in enumerate(gammas):
            input_vec.append(([(sk, Gpn.get_hecke_ti(g,gamma,reps = tuple(Up_reps_bar))) for sk, g in zip(repslocal_bar, Up_reps_bar)], c, j))

        vals = [V(0,normalize=False) for gamma in gammas]
        for lst, c, j in input_vec:
            outp = V(0, normalize=False)
            for sk, tt in lst:
                progress += pb_fraction
                outp += sk * c.evaluate(tt)
                update_progress(float(progress), 'Up action (%s)'%(2 * len(repslocal) * len(input_vec)))
            vals[j] += outp
        ans = self(vals)

        if scale != 1:
            ans = scale * ans
        return ans

    def improve(self, Phi, prec = None, sign = None, parallelize = False,progress_bar = False,method = 'naive', steps = 1):
        r"""

        Repeatedly applies U_p. Used in lifting theorems: 'improves' the precision of
        an overconvergent lift.

        (Applies the Bianchi version of Greenberg's lifting idea)

        """
        U = self.coefficient_module()
        group = self.group()
        if prec is None:
            prec = U.base_ring().precision_cap()
        assert prec is not None

        pi, pi_bar = self.P_gen, self.Pbar_gen
        p = pi.norm()
        if method != 'naive':
            raise NotImplementedError

        h2 = self.apply_Up(Phi, group = group, scale = sign,progress_bar = progress_bar)

        if progress_bar:
            update_progress(float(0)/float(prec),'f|Up')
        else:
            verbose('Applied Up once')

        ii = 0
        current_val = min([(u-v).valuation() for u,v in zip(h2.values(),Phi.values())])
        if progress_bar:
            update_progress(float(current_val)/float(prec),'f|Up')
        else:
            verbose("Applied Up once")
        old_val = current_val - 1
        while ii < 3 or (current_val < prec and current_val > old_val):
            h1 = h2
            old_val = current_val
            ii += 1
            h2 = self.apply_Up(h1, group = group, scale = sign,progress_bar = progress_bar)

            if progress_bar:
                update_progress(float(current_val)/float(prec),'f|Up')
            verbose('Applied Up %s times (val = %s)'%(ii+1,current_val))
            current_val = min([(u-v).valuation() for u,v in zip(h2.values(),h1.values())])
            if ii == 2 and current_val <= old_val:
                raise RuntimeError("Not converging, maybe ap sign is wrong?")
            if progress_bar and ii + 1 <= prec:
                update_progress(float(current_val)/float(prec),'f|Up')
            verbose('Applied Up %s times (val = %s)'%(ii+1,current_val))
        Phi._val = h2._val
        if progress_bar and current_val < 1:
            update_progress(float(1.0),'f|Up')
        return h2

class ArithCoh(ArithCoh_generic):
    def __init__(self, G, base = None, use_ps_dists = False):
        self._overconvergent = 0
        if base is None:
            base = ZZ
        self._pN = None
        V = base**1
        trivial_action = True

    def _element_constructor_(self,data):
        if isinstance(data,list):
            V = self.coefficient_module()
            return self.element_class(self, [V(o) for o in data])
        elif isinstance(data,self.element_class):
            G = self.group()
            V = self.coefficient_module()
            prec = None
            try:
                data = data.get_liftee()
            except AttributeError:
                pass
            try:
                vals = [V(data.evaluate(g).moment(0), normalize=False).lift(M=prec) for g in G.gens()]
            except (AttributeError, TypeError):
                try:
                    vals = [V(data.evaluate(g), normalize=False).lift(M=prec) for g in G.gens()]
                except (AttributeError, TypeError):
                    vals = [V(data.evaluate(g)) for g in G.gens()]
            return self.element_class(self, vals)
        else:
            G = self.group()
            V = self.coefficient_module()
            return self.element_class(self, [V(data) for g in G.gens()])

    def get_cocycle_from_elliptic_curve(self,E,sign = 1,use_magma = True):
        if sign == 0:
            return self.get_cocycle_from_elliptic_curve(E,1,use_magma) + self.get_cocycle_from_elliptic_curve(E,-1,use_magma)
        if not sign in [1, -1]:
            raise NotImplementedError
        F = self.group().base_ring()
        if F.signature()[1] == 0 or (F.signature() == (0,1) and 'G' not in self.group()._grouptype):
            K = (self.hecke_matrix(oo).transpose()-sign).kernel().change_ring(QQ)
        else:
            K = Matrix(QQ,self.dimension(),self.dimension(),0).kernel()
        disc = self.S_arithgroup().Gpn._O_discriminant
        discnorm = disc.norm()
        try:
            N = ZZ(discnorm.gen())
        except AttributeError:
            N = ZZ(discnorm)

        if F == QQ:
            x = QQ['x'].gen()
            F = NumberField(x,names='a')
            E = E.change_ring(F)

        def getap(q):
            if F == QQ:
                return E.ap(q)
            else:
                Q = F.ideal(q).factor()[0][0]
                return ZZ(Q.norm() + 1 - E.reduction(Q).count_points())

        q = ZZ(1)
        g0 = None
        while K.dimension() > 1:
            q = q.next_prime()
            for qq,e in F.ideal(q).factor():
                if  ZZ(qq.norm()).is_prime() and not qq.divides(F.ideal(disc.gens_reduced()[0])):
                    try:
                        ap = getap(qq)
                    except (ValueError,ArithmeticError):
                        continue
                    try:
                        K1 = (self.hecke_matrix(qq.gens_reduced()[0],g0 = g0,use_magma = use_magma).transpose()-ap).kernel()
                    except RuntimeError:
                        continue
                    K = K.intersection(K1)
        if K.dimension() != 1:
            raise ValueError,'Did not obtain a one-dimensional space corresponding to E'
        col = [ZZ(o) for o in (K.denominator()*K.matrix()).list()]
        return sum([a * self.gen(i) for i,a in enumerate(col) if a != 0],self(0))

    def get_rational_cocycle_from_ap(self,getap,sign = 1,use_magma = True):
        F = self.group().base_ring()
        if F.signature()[1] == 0 or (F.signature() == (0,1) and 'G' not in self.group()._grouptype):
            K = (self.hecke_matrix(oo).transpose()-sign).kernel().change_ring(QQ)
        else:
            K = Matrix(QQ,self.dimension(),self.dimension(),0).kernel()

        disc = self.S_arithgroup().Gpn._O_discriminant
        discnorm = disc.norm()
        try:
            N = ZZ(discnorm.gen())
        except AttributeError:
            N = ZZ(discnorm)

        if F == QQ:
            x = QQ['x'].gen()
            F = NumberField(x,names='a')
        q = ZZ(1)
        g0 = None
        while K.dimension() > 1:
            q = q.next_prime()
            for qq,e in F.ideal(q).factor():
                if  ZZ(qq.norm()).is_prime() and not qq.divides(F.ideal(disc.gens_reduced()[0])):
                    try:
                        ap = getap(qq)
                    except (ValueError,ArithmeticError):
                        continue
                    try:
                        K1 = (self.hecke_matrix(qq.gens_reduced()[0],g0 = g0,use_magma = use_magma).transpose()-ap).kernel()
                    except RuntimeError:
                        continue
                    K = K.intersection(K1)
        if K.dimension() != 1:
            raise ValueError,'Group does not have the required system of eigenvalues'

        col = [ZZ(o) for o in (K.denominator()*K.matrix()).list()]
        return sum([ a * self.gen(i) for i,a in enumerate(col) if a != 0], self(0))

    def get_rational_cocycle(self,sign = 1,use_magma = True,bound = 3, return_all = False):
        F = self.group().base_ring()
        if F.signature()[1] == 0 or (F.signature()[1] == 1 and 'G' not in self.group()._grouptype):
            K = (self.hecke_matrix(oo).transpose()-sign).kernel().change_ring(QQ)
        else:
            K = Matrix(QQ,self.dimension(),self.dimension(),0).kernel()

        component_list = []
        good_components = []
        if K.dimension() == 1:
            good_components.append(K)
        else:
            component_list.append(K)

        disc = self.S_arithgroup().Gpn._O_discriminant
        discnorm = disc.norm()
        try:
            N = ZZ(discnorm.gen())
        except AttributeError:
            N = ZZ(discnorm)

        if F == QQ:
            x = QQ['x'].gen()
            F = NumberField(x,names='a')
        q = ZZ(1)
        g0 = None
        num_hecke_operators = 0
        while len(component_list) > 0 and num_hecke_operators < bound:
            verbose('num_hecke_ops = %s'%num_hecke_operators)
            verbose('len(components_list) = %s'%len(component_list))
            q = q.next_prime()
            for qq,e in F.ideal(q).factor():
                if  ZZ(qq.norm()).is_prime() and not qq.divides(F.ideal(disc.gens_reduced()[0])):
                    try:
                        Aq = self.hecke_matrix(qq.gens_reduced()[0],g0 = g0,use_magma = use_magma).transpose().change_ring(QQ)
                    except (RuntimeError,TypeError) as e:
                        continue
                    verbose('Computed hecke matrix at qq = %s'%qq)
                    old_component_list = component_list
                    component_list = []
                    num_hecke_operators += 1
                    for U in old_component_list:
                        V = Aq.decomposition_of_subspace(U)
                        for U0,is_irred in V:
                            if Aq.restrict(U0).eigenvalues()[0] == ZZ(qq.norm()) + 1:
                                continue # Do not take Eisenstein classes.
                            if U0.dimension() == 1:
                                good_components.append(U0)
                            elif is_irred:
                                # Bad
                                continue
                            else: # U0.dimension() > 1 and not is_irred
                                component_list.append(U0)
                    if len(good_components) > 0 and not return_all:
                        K = good_components[0]
                        col = [ZZ(o) for o in (K.denominator()*K.matrix()).list()]
                        return sum([a*self.gen(i) for i,a in enumerate(col) if a != 0],self(0))
                    if len(component_list) == 0 or num_hecke_operators >= bound:
                        break

        if len(good_components) == 0:
            raise ValueError('Group does not seem to be attached to an elliptic curve')
        else:
            if return_all:
                ans = []
                for K in good_components:
                    col = [ZZ(o) for o in (K.denominator()*K.matrix()).list()]
                    ans.append( sum([a*self.gen(i) for i,a in enumerate(col) if a != 0],self(0)))
                return ans
            else:
                K = good_components[0]
                col = [ZZ(o) for o in (K.denominator()*K.matrix()).list()]
                return sum([ a * self.gen(i) for i,a in enumerate(col) if a != 0], self(0))

    def get_twodim_cocycle(self,sign = 1,use_magma = True,bound = 5, hecke_data = None, return_all = False, outfile = None):
        F = self.group().base_ring()
        if F == QQ:
            F = NumberField(PolynomialRing(QQ,'x').gen(),names='r')
        component_list = []
        good_components = []
        if F.signature()[1] == 0 or (F.signature() == (0,1) and 'G' not in self.group()._grouptype):
            Tinf = self.hecke_matrix(oo).transpose()
            K = (Tinf-sign).kernel().change_ring(QQ)
            if K.dimension() >= 2:
                component_list.append((K, [(oo,Tinf)]))
            fwrite('Too charpoly = %s'%Tinf.charpoly().factor(),outfile)
        else:
            K = Matrix(QQ,self.dimension(),self.dimension(),0).kernel()
            if K.dimension() >= 2:
                component_list.append((K, []))
        disc = self.S_arithgroup().Gpn._O_discriminant
        discnorm = disc.norm()
        try:
            N = ZZ(discnorm.gen())
        except AttributeError:
            N = ZZ(discnorm)

        if F == QQ:
            x = QQ['x'].gen()
            F = NumberField(x,names='a')
        q = ZZ(1)
        g0 = None
        num_hecke_operators = 0
        if hecke_data is not None:
            qq = F.ideal(hecke_data[0])
            pol = hecke_data[1]
            Aq = self.hecke_matrix(qq.gens_reduced()[0], use_magma = use_magma).transpose().change_ring(QQ)
            fwrite('ell = (%s,%s), T_ell charpoly = %s'%(qq.norm(), qq.gens_reduced()[0], Aq.charpoly().factor()),outfile)
            U0 = component_list[0][0].intersection(pol.subs(Aq).left_kernel())
            if U0.dimension() != 2:
                raise ValueError('Hecke data does not suffice to cut out space')
            good_component = (U0.denominator() * U0,component_list[0][1] + [(qq.gens_reduced()[0],Aq)])
            row0 = good_component[0].matrix().rows()[0]
            col0 = [QQ(o) for o in row0.list()]
            clcm = lcm([o.denominator() for o in col0])
            col0 = [ZZ(clcm * o ) for o in col0]
            flist = []
            for row0 in good_component[0].matrix().rows():
                col0 = [QQ(o) for o in row0.list()]
                clcm = lcm([o.denominator() for o in col0])
                col0 = [ZZ(clcm * o ) for o in col0]
                flist.append(sum([a * phi for a,phi in zip(col0,self.gens())],self(0)))
            return flist,[(ell, o.restrict(good_component[0])) for ell, o in good_component[1]]
        while len(component_list) > 0 and num_hecke_operators < bound:
            verbose('num_hecke_ops = %s'%num_hecke_operators)
            verbose('len(components_list) = %s'%len(component_list))
            q = q.next_prime()
            verbose('q = %s'%q)
            fact = F.ideal(q).factor()
            dfact = F.ideal(disc.gens_reduced()[0]).factor()
            for qq,e in fact:
                verbose('Trying qq = %s'%qq)
                if qq in [o for o,_ in dfact]:
                    verbose('Skipping because qq divides D...')
                    continue
                if  ZZ(qq.norm()).is_prime() and not qq.divides(F.ideal(disc.gens_reduced()[0])):
                    try:
                        Aq = self.hecke_matrix(qq.gens_reduced()[0],g0 = g0,use_magma = use_magma).transpose().change_ring(QQ)
                    except (RuntimeError,TypeError) as e:
                        verbose('Skipping qq (=%s) because Hecke matrix could not be computed...'%qq.gens_reduced()[0])
                        continue
                    except KeyboardInterrupt:
                        verbose('Skipping qq (=%s) by user request...'%qq.gens_reduced()[0])
                        num_hecke_operators += 1
                        sleep(1)
                        continue
                    verbose('Computed hecke matrix at qq = %s'%qq)
                    fwrite('ell = (%s,%s), T_ell charpoly = %s'%(qq.norm(), qq.gens_reduced()[0], Aq.charpoly().factor()),outfile)
                    old_component_list = component_list
                    component_list = []
                    num_hecke_operators += 1
                    for U,hecke_data in old_component_list:
                        V = Aq.decomposition_of_subspace(U)
                        for U0,is_irred in V:
                            if U0.dimension() == 1:
                                continue
                            if U0.dimension() == 2 and is_irred:
                                good_components.append((U0.denominator() * U0,hecke_data+[(qq.gens_reduced()[0],Aq)]))
                            else: # U0.dimension() > 2 or not is_irred
                                component_list.append((U0.denominator() * U0,hecke_data + [(qq.gens_reduced()[0],Aq)]))
                    if len(good_components) > 0 and not return_all:
                        flist = []
                        for row0 in good_components[0][0].matrix().rows():
                            col0 = [QQ(o) for o in row0.list()]
                            clcm = lcm([o.denominator() for o in col0])
                            col0 = [ZZ(clcm * o ) for o in col0]
                            flist.append(sum([a * phi for a,phi in zip(col0,self.gens())],self(0)))
                        return flist,[(ell, o.restrict(good_components[0][0])) for ell, o in good_components[0][1]]
                    if len(component_list) == 0 or num_hecke_operators >= bound:
                        break

        if len(good_components) == 0:
            if not return_all:
                raise ValueError('Group does not seem to be attached to an abelian surface')
            else:
                return []
        if return_all:
            ans = []
            for K,hecke_data in good_components:
                flist = []
                for row0 in K.matrix().rows():
                    col0 = [QQ(o) for o in row0.list()]
                    clcm = lcm([o.denominator() for o in col0])
                    col0 = [ZZ(clcm * o ) for o in col0]
                    flist.append(sum([a * phi for a,phi in zip(col0,self.gens())],self(0)))
                ans.append((flist,[(ell, o.restrict(K)) for ell, o in hecke_data]))
            return ans
        else:
            flist = []
            for row0 in good_components[0][0].matrix().rows():
                col0 = [QQ(o) for o in row0.list()]
                clcm = lcm([o.denominator() for o in col0])
                col0 = [ZZ(clcm * o ) for o in col0]
                flist.append(sum([a * phi for a,phi in zip(col0,self.gens())],self(0)))
            return flist,[(ell, o.restrict(good_components[0][0])) for ell, o in good_components[0][1]]

