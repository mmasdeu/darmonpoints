######################
##                  ##
##    ARITHMETIC    ##
##    COHOMOLOGY    ##
##                  ##
######################
r'''

TESTS:

sage: %runfile findcurve.sage
sage: F.<r> = QuadraticField(5)
sage: P = F.ideal(3/2*r + 1/2)
sage: D = F.ideal(3)
sage: from cohomology_abstract import *
sage: from sarithgroup import *
sage: from util import *
sage: from cohomology_arithmetic import *
sage: abtuple = quaternion_algebra_invariants_from_ramification(F,D,F.real_places()[:1])
sage: G = BigArithGroup(P,abtuple, F.ideal(1), grouptype = 'PSL2')
sage: CohShapiro = CohomologyGroup(G.Gn,CoIndModule(G,ZZ**1,trivial_action = True),trivial_action = False)
sage: CohOrig = CohomologyGroup(G.Gpn, ZZ**1, trivial_action = True)
sage: H = ArithCoh(G)
sage: primes = F.primes_of_degree_one_list(10)
sage: H.hecke_matrix(primes[0])
sage: ell = F.ideal(1/2*r + 5/2)
sage: H.hecke_matrix(ell)
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
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,LaurentSeriesRing,lcm, Qp,Zp,Zmod
from collections import defaultdict
from itertools import product,chain,izip,groupby,islice,tee,starmap
from sigma0 import Sigma0,Sigma0ActionAdjuster
from sage.rings.infinity import Infinity
from sage.rings.arith import GCD
from util import *
import os
from ocmodule import OCVn
from sage.misc.persist import db,db_save
from sage.schemes.plane_curves.constructor import Curve
from sage.parallel.decorate import fork,parallel
oo = Infinity
from sage.matrix.constructor import block_matrix
from sage.rings.number_field.number_field import NumberField
from sage.categories.action import Action
import operator
from cohomology_abstract import *
from sage.matrix.matrix_space import MatrixSpace
from ocmodule import our_adjuster, Sigma0Action
from sage.rings.arith import XGCD
from sage.modules.free_module_element import free_module_element, vector
from representations import *

def find_newans(Coh,glocs,ti):
    gens = Coh.group().gens()
    V = Coh.coefficient_module()
    N = len(V(0)._moments.list())
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

def get_overconvergent_class_matrices(p,E,prec,sign_at_infinity,use_ps_dists = False,use_sage_db = False,parallelize = False,progress_bar = False):
    # If the moments are pre-calculated, will load them. Otherwise, calculate and
    # save them to disk.
    from sage.misc.persist import db_save
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
    from pollack_stevens.space import ps_modsym_from_elliptic_curve
    phi0 = ps_modsym_from_elliptic_curve(E)
    if sign_at_infinity == 1:
        phi0 = phi0.plus_part()
    else:
        phi0 = phi0.minus_part()
    phi0 = 1/GCD([val.moment(0) for val in phi0.values()]) * phi0
    if progress_bar:
        progress_bar = update_progress
    else:
        progress_bar = None
    Phi = phi0.lift(p,M = prec - 1,algorithm = 'stevens',eigensymbol = True,progress_bar = progress_bar)
    db_save(Phi,fname)
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
        method = 'bigmatrix'
    else:
        if method != 'naive' and method != 'bigmatrix':
            raise ValueError('method should be either "naive" or "bigmatrix"')
    if Pnorm != p:
        raise NotImplementedError('For now I can only work over totally split')

    base_ring = Zp(p,prec) #Qp(p,prec)

    sgninfty = 'plus' if sign_at_infinity == 1 else 'minus'
    dist_type = 'ps' if use_ps_dists == True else 'fm'
    fname = 'moments_%s_%s_%s_%s_%s.sobj'%(p,Ename,sgninfty,prec,dist_type)
    if use_sage_db:
        try:
            Phivals = db(fname)
            CohOC = ArithCoh(G,overconvergent = True,base = base_ring,use_ps_dists = use_ps_dists)
            CohOC._coeff_module = Phivals[0].parent()
            VOC = CohOC.coefficient_module()
            Phi = CohOC([VOC(o) for o in Phivals])
            return Phi
        except IOError: pass
    verbose('Computing moments...')
    CohOC = ArithCoh(G,overconvergent = True,base = base_ring,use_ps_dists = use_ps_dists)
    VOC = CohOC.coefficient_module()
    Phi0 = CohOC(phiE) # [VOC(o) for o in phiE.values()])
    verbose('Now lifting...')
    Phi = CohOC.improve(Phi0, prec = prec,sign = sign_ap, parallelize = parallelize,progress_bar = progress_bar,method = method)
    if use_sage_db:
        raise NotImplementedError
        # db_save(Phi._val,fname)
    verbose('Done.')
    Phi.set_liftee(phiE)
    return Phi

class ArithAction(Action):
    def __init__(self,G,M):
        Action.__init__(self,G,M,is_left = True,op = operator.mul)

    def _call_(self,g,v):
        V = v.parent()
        g = g.embed(V.precision_cap())
        try:
            return g * v
        except TypeError:
            S0 = V.Sigma0()
            return S0(g, check = False) * v

class LocalAction(Action):
    def __init__(self,G,M):
        self.G = G
        Action.__init__(self,G.large_group().B,M,is_left = True,op = operator.mul)

    def _call_(self,g,v):
        V = v.parent()
        return V.Sigma0()(self.G.embed(g, V.precision_cap()), check = False) * v

class ArithCohElement(CohomologyElement):
    def set_liftee(self,x):
        self._liftee = x

    def get_liftee(self):
        try:
            return self._liftee
        except AttributeError:
            raise RuntimeError,"Don't know what this cocycle is a lift of!"
    def _repr_(self):
        return 'Arithmetic cohomology class in %s'%self.parent()

class ArithCoh(CohomologyGroup):
    Element = ArithCohElement
    def __init__(self,G,overconvergent = False,base = None,use_ps_dists = False):
        self._S_arithgroup = G
        self._use_ps_dists = use_ps_dists
        self._use_shapiro = G._use_shapiro
        if overconvergent and base is None:
            raise ValueError, 'Must give base if overconvergent'
        if base is None:
            base = ZZ
        if overconvergent:
            trivial_action = False
            if self._use_ps_dists:
                from pollack_stevens.distributions import Distributions, Symk
                V = Distributions(0,base = base, prec_cap = base.precision_cap(), act_on_left = True,adjuster = our_adjuster(), dettwist = 0) # Darmon convention
                V.Sigma0 = lambda :V._act._Sigma0
            else:
                V = OCVn(base.prime(), 1 + base.precision_cap())
            if self._use_shapiro:
                V._arith_act = ArithAction(G.large_group(), V)
            else:
                V._arith_act = ArithAction(G.small_group(), V)
            V._local_act = LocalAction(G, V)
            V._unset_coercions_used()
            V.register_action( V._arith_act )
            V.register_action( V._local_act )
            self._pN = V._p**base.precision_cap()
        else:
            self._pN = None
            V = base**1
            trivial_action = True
        if self._use_shapiro:
            CohomologyGroup.__init__(self, G.large_group(), CoIndModule(G,V,trivial_action = trivial_action), False)
        else:
            CohomologyGroup.__init__(self, G.small_group(), V, trivial_action)

    def use_shapiro(self):
        return self._use_shapiro

    def S_arithgroup(self):
        return self._S_arithgroup

    def _element_constructor_(self,data):
        if isinstance(data,list):
            return self.element_class(self, data)
        elif isinstance(data,self.element_class):
            G = self.group()
            V = self.coefficient_module()
            try:
                data = data.get_liftee()
                return self.element_class(self,[V(data.evaluate(g).moment(0)) for g in G.gens()])
            except RuntimeError:
                return self.element_class(self,[V(data.evaluate(g)) for g in G.gens()])
        else:
            G = self.group()
            V = self.coefficient_module()
            return self.element_class(self, [V(data) for g in G.gens()])

    def improve(self, Phi, prec = None, sign = None, parallelize = False,progress_bar = False,method = 'bigmatrix'):
        r"""
        Repeatedly applies U_p.

        EXAMPLES::

        """
        U = self.coefficient_module()
        group = self.group()
        if prec is None:
            prec = U.base_ring().precision_cap()
        assert prec is not None
        repslocal = self.get_Up_reps_local(prec)
        if method == 'naive':
            h2 = self.apply_Up(Phi, group = group, scale = 1,parallelize = parallelize,times = 0,progress_bar = False,method = 'naive')
            if progress_bar:
                update_progress(float(0)/float(prec),'f|Up')
            else:
                verbose('Applied Up %s times (val = %s)'%(1,current_val))

            h2 = self.apply_Up(h2, group = group, scale = 1,parallelize = parallelize,times = 0,progress_bar = False,method = 'naive')
            if progress_bar:
                update_progress(1.0/float(prec),'f|Up')
            else:
                verbose("Applied Up twice")
            ii = 0
            try:
                current_val = min([(u-v).valuation() for u,v in zip([o for w in h2.values() for o in w.values()],[o for w in Phi.values() for o in w.values()])])
            except AttributeError:
                current_val = min([(u-v).valuation() for u,v in zip(h2.values(),Phi.values())])
            old_val = current_val - 1
            while current_val < prec and current_val > old_val:
                h1 = h2
                old_val = current_val
                ii += 2
                h2 = self.apply_Up(h1, group = group, scale = 1,parallelize = parallelize,times = 0,progress_bar = False,method = 'naive')
                if progress_bar:
                    update_progress(float(ii)/float(prec),'f|Up')
                else:
                    verbose('Applied Up %s times (val = %s)'%(ii+1,current_val))
                h2 = self.apply_Up(h2, group = group, scale = 1,parallelize = parallelize,times = 0,progress_bar = False,method = 'naive')
                try:
                    current_val = min([(u-v).valuation() for u,v in zip([o for w in h2.values() for o in w.values()],[o for w in h1.values() for o in w.values()])])
                except AttributeError:
                    current_val = min([(u-v).valuation() for u,v in zip(h2.values(),h1.values())])
                if ii == 2 and current_val <= old_val:
                    raise RuntimeError("Not converging, maybe ap sign is wrong?")
                if progress_bar:
                    update_progress(float(ii+1)/float(prec),'f|Up')
                else:
                    verbose('Applied Up %s times (val = %s)'%(ii+2,current_val))
            Phi._val = h2._val
            return h2
        else:
            assert method == 'bigmatrix'
            return self.apply_Up(Phi, group = group, scale = 1, parallelize = parallelize,times = len(ZZ(prec-1).bits()),progress_bar = progress_bar,method = 'bigmatrix',repslocal = repslocal)

    @cached_method
    def hecke_matrix(self, l, use_magma = True, g0 = None): # l can be oo
        dim = self.dimension()
        R = self.coefficient_module().base_ring()
        M = matrix(R,dim,dim,0)
        for j,cocycle in enumerate(self.gens()):
            # Construct column j of the matrix
            fvals = self.apply_hecke_operator(cocycle, l, use_magma = use_magma, g0 = g0)
            M.set_column(j,list(vector(fvals)))
        return M

    def get_cocycle_from_elliptic_curve(self,E,sign = 1,use_magma = True):
        F = self.group().base_ring()
        if F.signature()[1] == 0 or (F.signature() == (0,1) and 'G' not in self.group()._grouptype):
            K = (self.hecke_matrix(oo)-sign).right_kernel()
        else:
            K = Matrix(QQ,self.dimension(),self.dimension(),0).right_kernel()
        disc = self.group()._O_discriminant
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
                    K1 = (self.hecke_matrix(qq.gens_reduced()[0],g0 = g0,use_magma = use_magma)-ap).right_kernel()
                    K = K.intersection(K1)
        if K.dimension() != 1:
            raise ValueError,'Did not obtain a one-dimensional space corresponding to E'
        col = [ZZ(o) for o in (K.denominator()*K.matrix()).list()]
        return sum([a * self.gen(i) for i,a in enumerate(col) if a != 0],self(0))

    def get_rational_cocycle_from_ap(self,getap,sign = 1,use_magma = True):
        F = self.group().base_ring()
        if F.signature()[1] == 0 or (F.signature() == (0,1) and 'G' not in self.group()._grouptype):
            K = (self.hecke_matrix(oo)-sign).right_kernel()
        else:
            K = Matrix(QQ,self.dimension(),self.dimension(),0).right_kernel()

        disc = self.group()._O_discriminant
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
                    K1 = (self.hecke_matrix(qq.gens_reduced()[0],g0 = g0,use_magma = use_magma)-ap).right_kernel()
                    K = K.intersection(K1)
        if K.dimension() != 1:
            raise ValueError,'Group does not have the required system of eigenvalues'

        col = [ZZ(o) for o in (K.denominator()*K.matrix()).list()]
        return sum([ a * self.gen(i) for i,a in enumerate(col) if a != 0], self(0))

    def get_rational_cocycle(self,sign = 1,use_magma = True,bound = 3, return_all = False):
        F = self.group().base_ring()
        if F.signature()[1] == 0 or (F.signature() == (0,1) and 'G' not in self.group()._grouptype):
            K = (self.hecke_matrix(oo)-sign).right_kernel().change_ring(QQ)
        else:
            K = Matrix(QQ,self.dimension(),self.dimension(),0).right_kernel()

        component_list = []
        good_components = []
        if K.dimension() == 1:
            good_components.append(K)
        else:
            component_list.append(K)

        disc = self.group()._O_discriminant
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

    def get_twodim_cocycle(self,sign = 1,use_magma = True,bound = 3, pol = None, return_all = False):
        F = self.group().base_ring()
        if F.signature()[1] == 0 or (F.signature() == (0,1) and 'G' not in self.group()._grouptype):
            K = (self.hecke_matrix(oo)-sign).right_kernel().change_ring(QQ)
        else:
            K = Matrix(QQ,self.dimension(),self.dimension(),0).right_kernel()

        component_list = []
        good_components = []
        if K.dimension() == 2:
            good_components.append((K, []))
        elif K.dimension() >= 2:
            component_list.append((K, []))

        disc = self.group()._O_discriminant
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
                    for U,hecke_data in old_component_list:
                        V = Aq.decomposition_of_subspace(U)
                        for U0,is_irred in V:
                            if U0.dimension() == 1:
                                continue
                            if U0.dimension() == 2 and is_irred:
                                if pol is None or Aq.restrict(U0).charpoly() == pol:
                                    good_components.append((U0.denominator() * U0,hecke_data+[(qq.gens_reduced()[0],Aq)]))
                            else: # U0.dimension() > 2 or not is_irred
                                component_list.append((U0,hecke_data + [(qq.gens_reduced()[0],Aq)]))
                    if len(good_components) > 0 and not return_all:
                        flist = []
                        for row0 in good_components[0][0].matrix().rows():
                            col0 = [ZZ(o) for o in row0.list()]
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
                    col0 = [ZZ(o) for o in row0.list()]
                    flist.append(sum([a * phi for a,phi in zip(col0,self.gens())],self(0)))
                ans.append((flist,[(ell, o.restrict(K)) for ell, o in hecke_data]))
            return ans
        else:
            flist = []
            for row0 in good_components[0][0].matrix().rows():
                col0 = [ZZ(o) for o in row0.list()]
                flist.append(sum([a * phi for a,phi in zip(col0,self.gens())],self(0)))
            return flist,[(ell, o.restrict(good_components[0][0])) for ell, o in good_components[0][1]]

    def apply_hecke_operator(self,c,l, hecke_reps = None,group = None,scale = 1,use_magma = True,g0 = None):
        r"""
        Apply the l-th Hecke operator operator to ``c``.

        EXAMPLES::

        """
        # verbose('Entering apply_hecke_operator')
        if hecke_reps is None:
            hecke_reps = self.group().get_hecke_reps(l,use_magma = use_magma) # Assume l != p here!
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
            for g in hecke_reps:
                if self.trivial_action():
                    vals[j] += c.evaluate(group.get_hecke_ti(g,gamma,l,use_magma))
                else:
                    vals[j] += g * c.evaluate(group.get_hecke_ti(g,gamma,l,use_magma))
        return scale * self(vals)

    def get_Up_reps_local(self,prec):
        assert prec is not None
        V = self.coefficient_module()
        try:
            V = V.coefficient_module()
        except AttributeError:
            pass
        S0 = V.Sigma0()
        return [S0(self.group().embed(g,prec), check = False) for g in self.S_arithgroup().get_Up_reps()]

    def apply_Up(self,c,group = None,scale = 1,parallelize = False,times = 0,progress_bar = False,method = 'bigmatrix', repslocal = None):
        r"""
        Apply the Up Hecke operator operator to ``c``.

        EXAMPLES::

        """
        Up_reps = self.S_arithgroup().get_Up_reps()

        V = self.coefficient_module()
        R = V.base_ring()
        gammas = self.group().gens()

        if repslocal is None:
            try:
                prec = V.base_ring().precision_cap()
            except AttributeError:
                prec = None
            repslocal = self.get_Up_reps_local(prec)

        if method == 'naive':
            assert times == 0
            G = self.S_arithgroup()
            Gn = G.large_group()
            if self.use_shapiro():
                def calculate_Up_contribution(lst, c, i, j):
                    return sum([sk * c.evaluate_and_identity(tt) for sk, tt in lst])
                input_vec = []
                for j, gamma in enumerate(gammas):
                    for i, xi in enumerate(G.coset_reps()):
                        delta = Gn(G.get_coset_ti(set_immutable(xi * gamma.quaternion_rep))[0])
                        input_vec.append(([(sk, Gn.get_hecke_ti(g,delta)) for sk, g in zip(repslocal, Up_reps)], c, i, j))
                vals = [[V.coefficient_module()(0) for xi in G.coset_reps()] for gamma in gammas]
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
                def calculate_Up_contribution(lst,c,num_gamma):
                    return sum([sk * c.evaluate(tt) for sk, tt in lst])
                input_vec = []
                for j,gamma in enumerate(gammas):
                    input_vec.append(([(sk, Gpn.get_hecke_ti(g,gamma)) for sk, g in zip(repslocal, Up_reps)], c, j))
                vals = [V(0) for gamma in gammas]
                if parallelize:
                    for inp,outp in parallel(calculate_Up_contribution)(input_vec):
                        vals[inp[0][-1]] += outp
                else:
                    for inp in input_vec:
                        outp = calculate_Up_contribution(*inp)
                        vals[inp[-1]] += outp
                ans = self(vals)
            if scale != 1:
                ans = scale * ans
            return ans
        else:
            assert method == 'bigmatrix'
            verbose('Getting Up matrices...')
            N = len(V(0)._moments.list())
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
            return self([V(appr_module(valmat.submatrix(row=i,nrows = N).list())) for i in xrange(0,valmat.nrows(),N)])
