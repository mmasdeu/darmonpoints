######################
##                  ##
##    COHOMOLOGY    ##
##                  ##
######################
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

def find_newans(Coh,glocs,ti):
    G = Coh.group()
    newans = [glocs[0].new_matrix() for u in G.gens()]
    for gk,tik in zip(glocs,ti):
        fox_grad_k = Coh.fox_gradient(tik)
        for j,gj in enumerate(G.gens()):
            newans[j] += gk * fox_grad_k[j]
            newans[j] = newans[j].apply_map(lambda x: x % Coh._pN)
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
            CohOC = CohomologyGroup(G.small_group(),overconvergent = True,base = base_ring,use_ps_dists = use_ps_dists)
            CohOC._coeff_module = Phivals[0].parent()
            VOC = CohOC.coefficient_module()
            Phi = CohOC([VOC(o) for o in Phivals])
            return Phi
        except IOError: pass
    verbose('Computing moments...')
    CohOC = CohomologyGroup(G.small_group(),overconvergent = True,base = base_ring,use_ps_dists = use_ps_dists)
    VOC = CohOC.coefficient_module()
    if use_ps_dists:
        Phi = CohOC([VOC(QQ(phiE.evaluate(g)[0])).lift(M = prec) for g in G.small_group().gens()])
    else:
        Phi = CohOC([VOC(Matrix(VOC._R,VOC._depth,1,[phiE.evaluate(g)[0]]+[0 for i in xrange(VOC._depth - 1)]),check = False) for g in G.small_group().gens()])
    if progress_bar:
        verb_level = get_verbose()
    verbose('Now lifting...')
    Phi = Phi.improve(prec = prec,sign = sign_ap, parallelize = parallelize,progress_bar = progress_bar,method = method)
    if use_sage_db:
        db_save(Phi._val,fname)
    verbose('Done.')
    Phi.set_liftee(phiE)
    return Phi


class CohomologyElement(ModuleElement):
    def __init__(self, parent, data):
        r'''
        Define an element of `H^1(G,ZZ)`

        INPUT:
            - G: a BigArithGroup
            - V: a CoeffModule
            - data: a list

        TESTS:
            sage: G = BigArithGroup(5,6,1)
            sage: V = QQ^1
            sage: Coh = Cohomology(G,V)
            sage: print Coh.hecke_matrix(13).eigenvalues()
            [2,2]
            sage: print Coh.hecke_matrix(7).eigenvalues()
            [4,-4]
            sage: PhiE = Coh.gen(1)
        '''
        G = parent.group()
        V = parent.coefficient_module()
        if isinstance(data,list):
            self._val = [V(0) if o.is_zero() else V(o) for o in data]
        else:
            self._val = [V(data.evaluate(b)) for b in parent.group().gens()]
        if parent.is_overconvergent:
            self.evaluate = self.evaluate_oc
        else:
            self.evaluate = self.evaluate_triv
        ModuleElement.__init__(self,parent)

    def set_liftee(self,x):
        self._liftee = x
    def get_liftee(self):
        try:
            return self._liftee
        except AttributeError:
            raise RuntimeError,"Don't know what this cocycle is a lift of!"
    def values(self):
        return self._val

    def _repr_(self):
        return 'Cohomology class in %s'%self.parent()

    def  _add_(self,right):
        return self.__class__(self.parent(),[a+b for a,b in zip(self._val,right._val)])

    def  _sub_(self,right):
        return self.__class__(self.parent(),[a-b for a,b in zip(self._val,right._val)])

    def  _neg_(self):
        return self.__class__(self.parent(),[-a for a in self._val])

    def  __rmul__(self,right):
        return self.__class__(self.parent(),[ZZ(right) * a for a in self._val])

    def shapiro_image(self,G):
        if self.parent().is_overconvergent:
            raise TypeError,'This functionality is only for trivial coefficients'
        return ShapiroImage(G,self)

    @cached_method
    def evaluate_oc(self,x,parallelize = False,extramul = None):
        H = self.parent()
        if H._use_ps_dists:
            return self.evaluate_oc_naive(x,extramul = extramul)
        G = H.group()
        V = H.coefficient_module()
        prec = V.precision_cap()
        Sigma0 = H.Sigma0()
        if hasattr(x,'word_rep'):
            wd  = x.word_rep
        else:
            x = G(x)
            wd = x.word_rep
        if len(wd) == 0:
            return V(0)
        i,a = wd[-1]
        ans = H.eval_at_genpow(i,a,self._val)
        ans = ans.apply_map(lambda x: x % H._pN)
        for i,a in reversed(wd[:-1]):
            ans = H.eval_at_genpow(i,a,self._val) + H.mul_by_gen_pow(i,a,ans)
        if extramul is not None:
            ans = extramul * ans
            ans = ans.apply_map(lambda x: x % H._pN)
        return V(ans,check = False)

    def evaluate_triv(self,x,parallelize = False,extramul = None):
        try:
            word = tuple(x.word_rep)
        except AttributeError:
            word = tuple(self.parent().group()(x).word_rep)
        V = self.parent().coefficient_module()
        return sum([a*self._evaluate_at_group_generator(j) for j,a in word],V(0))

    def evaluate_oc_naive(self,x,extramul = None):
        try:
            word = tuple(x.word_rep)
        except AttributeError:
            word = tuple(self.parent().group()(x).word_rep)
        V = self.parent().coefficient_module()
        if len(word) == 0:
            return V(0)
        elif len(word) == 1:
            return self._evaluate_syllable(*word[0])
        else:
            return self._evaluate_word(word)

    @cached_method
    def _evaluate_at_group_generator(self,j): # j is the index in Gpn.gens()
        G = self.parent().group()
        Gab = G.abelianization()
        coeff_module = self.parent().coefficient_module()
        gablist = list(Gab.G_to_ab_free(G.gen(j)))
        cvals = [coeff_module(o) for o in self._val]
        ans = sum([ZZ(a0) * b for a0,b in zip(gablist,cvals) if a0 != 0],coeff_module(0))
        return ans

    def _evaluate_syllable(self,g,a):
        G = self.parent().group()
        V = self.parent().coefficient_module()
        prec = V.precision_cap()
        Sigma0 = self.parent().Sigma0()
        if a == 1:
            return self._val[g]
        elif a == 0:
            return V(0)
        elif a == -1:
            gmat_inv = G.gen(g).embed(prec).adjoint() # G.gen(g).embed(prec)**-1
            if self.parent()._use_ps_dists:
                return -(Sigma0(gmat_inv) * self._val[g])
            else:
                return  -self._val[g].l_act_by(gmat_inv)
        elif a < 0:
            gmat = G.gen(g).embed(prec)
            gmat_inv = gmat.adjoint() #gmat**-1
            phig = self._val[g]
            tmp = V(phig)
            if self.parent()._use_ps_dists:
                for i in xrange(-a-1):
                    tmp = phig + Sigma0(gmat) * tmp
                return -(Sigma0(gmat_inv**-a) * tmp)
            else:
                for i in xrange(-a-1):
                    tmp = phig + tmp.l_act_by(gmat)
                return -(tmp.l_act_by(gmat_inv**-a))
        else:
            gmat = G.gen(g).embed(prec)
            phig = self._val[g]
            tmp = V(phig)
            if self.parent()._use_ps_dists:
                for i in xrange(a-1):
                    tmp = phig + Sigma0(gmat) * tmp
            else:
                for i in xrange(a-1):
                    tmp = phig + tmp.l_act_by(gmat)
            return tmp

    def _evaluate_word(self,word):
        r''' Evaluate recursively, using cocycle condition:
        self(gh) = self(g) + g*self(h)
        This implies also that:
        1) self(g^a) = self(g^b) + g^b*self(g^(a-b)) (will apply it to b = a // 2, a > 0
        2) self(g^-1) = - g^(-1)*self(g)
        '''
        G = self.parent().group()
        V = self.parent().coefficient_module()
        prec = V.precision_cap()
        Sigma0 = self.parent().Sigma0()

        lenword = len(word)
        if lenword > 1:
            pivot = ZZ(lenword) // ZZ(2)
            word_prefix = word[:pivot]
            gammamat = G.embed(prod([G.Ugens[g]**a for g,a in word_prefix],G.B(1)),prec)
            if self.parent()._use_ps_dists:
                return self._evaluate_word(tuple(word_prefix)) + Sigma0(gammamat) *  self._evaluate_word(tuple(word[pivot:]))
            else:
                return self._evaluate_word(tuple(word_prefix)) +  self._evaluate_word(tuple(word[pivot:])).l_act_by(gammamat)

        if lenword == 0:
            return V(0)

        if lenword == 1:
            return self._evaluate_syllable(*word[0])

    def improve(self,prec = None,sign = 1, parallelize = False,progress_bar = False,method = 'bigmatrix'):
        r"""
        Repeatedly applies U_p.

        EXAMPLES::

        """
        U = self.parent().coefficient_module()
        p = U.prime()
        group = self.parent().group()
        if prec is None:
            prec = U.precision_cap()

        repslocal = self.parent().get_Up_reps_local(prec)
        if method == 'naive':
            h2 = self.parent().apply_Up(self, group = group, scale = sign,parallelize = parallelize,times = 0,progress_bar = False,method = 'naive')
            if progress_bar:
                update_progress(1.0/float(prec),'f|Up')
            else:
                verbose("Applied Up once")
            ii = 0
            m0val = min([(u.moment(0) - v.moment(0)).valuation(p) for u,v in zip(h2._val,self._val)])
            if m0val == 0:
                sign *= ZZ(-1)
                h2 = -h2
                m0val = min([(u.moment(0) - v.moment(0)).valuation(p) for u,v in zip(h2._val,self._val)])
                if m0val <= 0:
                    raise RuntimeError("Does not seem to converge")
            current_val = min([(u-v).valuation(p) for u,v in zip(h2._val,self._val)])
            old_val = current_val - 1
            while current_val < prec and current_val > old_val:
                h1 = h2
                old_val = current_val
                ii += 1
                h2 = self.parent().apply_Up(h1, group = group, scale = sign,parallelize = parallelize,times = 0,progress_bar = False,method = 'naive')
                current_val = min([(u-v).valuation(p) for u,v in zip(h2._val,h1._val)])
                if ii == 1 and current_val <= old_val:
                    raise RuntimeError("Not converging, maybe ap sign is wrong?")
                if progress_bar:
                    update_progress(float(ii+1)/float(prec),'f|Up')
                else:
                    verbose('Applied Up %s times (val = %s)'%(ii+1,current_val))
            self._val = h2._val
            return h2
        else:
            assert method == 'bigmatrix'
            return self.parent().apply_Up(self, group = group, scale = sign, parallelize = parallelize,times = len(ZZ(prec-1).bits()),progress_bar = progress_bar,method = 'bigmatrix',repslocal = repslocal)


class _our_adjuster(Sigma0ActionAdjuster):
    """
    Callable object that turns matrices into 4-tuples.

    EXAMPLES::

        sage: from sage.modular.btquotients.pautomorphicform import _btquot_adjuster
        sage: adj = _btquot_adjuster()
        sage: adj(matrix(ZZ,2,2,[1..4]))
        (4, 2, 3, 1)
    """
    def __call__(self, g):
        a,b,c,d = g.list()
        return tuple([d,b,c,a])

class CohomologyGroup(Parent):
    Element = CohomologyElement
    def __init__(self,G,overconvergent = False,base = None,use_ps_dists = False):
        self._group = G
        self._use_ps_dists = use_ps_dists
        if overconvergent and base is None:
            raise ValueError, 'Must give base if overconvergent'
        if base is None:
            base = ZZ
        if overconvergent:
            self.is_overconvergent = True
            if self._use_ps_dists:
                from sage.modular.pollack_stevens.distributions import Distributions, Symk
                self._coeffmodule = Distributions(0,base = base, prec_cap = base.precision_cap(), act_on_left = True,adjuster = _our_adjuster(), dettwist = 0) # Darmon convention
            else:
                self._coeffmodule = OCVn(base.prime(),1 + base.precision_cap())
                # self._coeffmodule = OCVn(0,base,1+base.precision_cap())
            self._num_abgens = len(self._group.gens())
            self._gen_pows = []
            self._gen_pows_neg = []
            onemat = matrix(ZZ,2,2,[1,0,0,1])
            onemat.set_immutable()
            try:
                one = self._coeffmodule._get_powers(onemat).parent().identity_matrix()
            except AttributeError:
                one = self._coeffmodule._get_powers(onemat).identity_matrix()
            for i,g in enumerate(self._group.gens()):
                gmat = self.group().embed(self._group.Ugens[i], 1 + base.precision_cap())
                gmat.set_immutable()
                A = self._coeffmodule._get_powers(gmat)
                self._gen_pows.append([one, A])
                # assert gmat.determinant() == 1
                gmatinv = gmat.adjoint() # gmat**-1
                gmatinv.set_immutable()
                Ainv = self._coeffmodule._get_powers(gmatinv)
                self._gen_pows_neg.append([one, Ainv])

            self._pN = self._coeffmodule._p**base.precision_cap()
        else:
            self._pN = 0
            self.is_overconvergent = False
            self._coeffmodule = base**1
            self._Ga = G.abelianization()
            self._V = self._Ga.ambient()
            self._num_abgens = len(self._Ga.free_gens())
            self._F = QQ**self._num_abgens
            self._space = Hom(self._F,self._coeffmodule)
        Parent.__init__(self)

    def group(self):
        return self._group

    def Sigma0(self):
        if self._use_ps_dists:
            return self._coeffmodule._act._Sigma0
        else:
            return (lambda x:x)

    def _repr_(self):
        return 'H^1(G,V), with G being %s and V = %s'%(self.group(),self.coefficient_module())

    def _an_element_(self):
        return self(0)

    def _coerce_map_from_(self,S):
        if isinstance(S,CohomologyGroup):
            return True
        else:
            return False

    def _element_constructor_(self,data):
        if isinstance(data,list):
            return self.element_class(self,data)
        elif isinstance(data,self.element_class):
            G = self.group()
            V = self.coefficient_module()
            if data.parent().is_overconvergent:
                try:
                    return self.element_class(self,[V(data.get_liftee().evaluate(g).moment(0)) for g in G.gens()])
                except RuntimeError:
                    return self.element_class(self,[V(data.evaluate(g).moment(0).rational_reconstruction()) for g in G.gens()])
            else:
                return self.element_class(self,[V(data.evaluate(g)) for g in G.gens()])
        else:
            return self.element_class(self,[self._coeffmodule(data) for g in xrange(self._num_abgens)])

    def fox_gradient(self,word):
        h = self.get_gen_pow(0,0)
        ans = [h.new_matrix() for o in self.group().gens()]
        if len(word) == 0:
            return ans
        lenword = len(word)
        for j in xrange(lenword):
            i,a = word[j]
            ans[i] += h  * self.get_fox_term(i,a)
            ans[i] = ans[i].apply_map(lambda x: x % self._pN)
            if j < lenword -1:
                h = h * self.get_gen_pow(i,a)
                h = h.apply_map(lambda x: x % self._pN)
        return ans

    def get_gen_pow(self,i,a):
        if a == 0:
            return self._gen_pows[0][0]
        elif a > 0:
            genpows = self._gen_pows[i]
        else:
            genpows = self._gen_pows_neg[i]
            a = -a
        while len(genpows) <= a:
            tmp = genpows[1] * genpows[-1]
            genpows.append(tmp.apply_map(lambda x:x % self._pN))
        return genpows[a]

    def get_fox_term(self,i,a):
        if a == 1:
            return self._gen_pows[i][0]
        elif a == -1:
            return -self._gen_pows_neg[i][1]
        elif a > 1:
            genpows = self._gen_pows[i]
            ans = genpows[0] + genpows[1]
            for o in xrange(a-2):
                ans = ans.apply_map(lambda x: x % self._pN)
                ans = genpows[0] + genpows[1] * ans
            ans = ans.apply_map(lambda x: x % self._pN)
            return ans
        elif a < -1:
            a = -a
            genpows = self._gen_pows_neg[i]
            ans = genpows[0] + genpows[1]
            for o in xrange(a-2):
                ans = ans.apply_map(lambda x: x % self._pN)
                ans = genpows[0] + genpows[1] * ans
            ans = -genpows[1] * ans
            ans = ans.apply_map(lambda x: x % self._pN)
            return ans

    def eval_at_genpow(self,i,a,v):
        v = v[i]._val
        if a == 1:
            return v
        elif a == -1:
            return - self._gen_pows_neg[i][1] * v
        elif a > 1:
            genpows = self._gen_pows[i]
            ans = v + genpows[1] * v
            for o in xrange(a-2):
                ans = ans.apply_map(lambda x: x % self._pN)
                ans = v + genpows[1] * ans
            ans = ans.apply_map(lambda x: x % self._pN)
            return ans
        elif a < -1:
            a = -a
            genpows = self._gen_pows_neg[i]
            ans = v + genpows[1] * v
            for o in xrange(a-2):
                ans = ans.apply_map(lambda x: x % self._pN)
                ans = v + genpows[1] * ans
            ans = -genpows[1] * ans
            ans = ans.apply_map(lambda x: x % self._pN)
            return ans

    def mul_by_gen_pow(self,i,a,v):
        ans = v
        if a == 0:
            return ans
        elif a > 0:
            g = self._gen_pows[i][1]
        else:
            g = self._gen_pows_neg[i][1]
            a = -a
        for o in xrange(a):
            ans = (g * ans).apply_map(lambda x: x % self._pN)
        return ans

    def dimension(self):
        raise NotImplementedError

    def coefficient_module(self):
        return self._coeffmodule

    def dimension(self): # Warning
        return len(self._space.basis())

    def gen(self,i): # Warning
        phi = self._space.basis()[i]
        dom = phi.domain()
        return self([phi(o) for o in dom.gens()])

    def gens(self): # Warning
        return [self.gen(i) for i in xrange(self.dimension())]

    @cached_method
    def hecke_matrix(self,l,use_magma = True,g0 = None):
        if self.coefficient_module().dimension() > 1:
            raise NotImplementedError
        dim = self.dimension()
        R = self.coefficient_module().base_ring()
        M = matrix(R,dim,dim,0)
        for j,cocycle in enumerate(self.gens()):
            # Construct column j of the matrix
            M.set_column(j,[o[0] for o in self.apply_hecke_operator(cocycle,l,use_magma = use_magma,g0 = g0).values()])
        return M

    @cached_method
    def involution_at_infinity_matrix(self):
        if self.coefficient_module().dimension() > 1:
            raise NotImplementedError
        H = self._space
        Gpn = self.group()
        Gab = self._Ga
        # x = Gpn.element_of_norm(-1,use_magma = False)
        x = Gpn.non_positive_unit()
        dim = self.dimension()
        M = matrix(QQ,dim,dim,0)
        assert len(self.gens()) == len(Gab.free_gens())
        for j,g0 in enumerate(Gab.free_gens()):
            # Construct column j of the matrix
            g = Gab.ab_to_G(g0).conjugate_by(x)
            M.set_column(j,list(Gab.G_to_ab_free(g)))
        return M.transpose()

    def get_cocycle_from_elliptic_curve(self,E,sign = 1,use_magma = True):
        F = self.group().base_ring()
        if F.signature()[1] == 0 or (F.signature() == (0,1) and 'G' not in self.group()._grouptype):
            K = (self.involution_at_infinity_matrix()-sign).right_kernel()
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
        return sum([a*self.gen(i) for i,a in enumerate(col) if a != 0],self(0))

    def get_rational_cocycle_from_ap(self,getap,sign = 1,use_magma = True):
        F = self.group().base_ring()
        if F.signature()[1] == 0 or (F.signature() == (0,1) and 'G' not in self.group()._grouptype):
            K = (self.involution_at_infinity_matrix()-sign).right_kernel()
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
        return sum([a*self.gen(i) for i,a in enumerate(col) if a != 0],self(0))

    def get_rational_cocycle(self,sign = 1,use_magma = True,bound = 3, return_all = False):
        F = self.group().base_ring()
        if F.signature()[1] == 0 or (F.signature() == (0,1) and 'G' not in self.group()._grouptype):
            K = (self.involution_at_infinity_matrix()-sign).right_kernel().change_ring(QQ)
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
                return sum([a*self.gen(i) for i,a in enumerate(col) if a != 0],self(0))


    def get_twodim_cocycle(self,sign = 1,use_magma = True,bound = 3, pol = None, return_all = False):
        F = self.group().base_ring()
        if F.signature()[1] == 0 or (F.signature() == (0,1) and 'G' not in self.group()._grouptype):
            K = (self.involution_at_infinity_matrix()-sign).right_kernel().change_ring(QQ)
        else:
            K = Matrix(QQ,self.dimension(),self.dimension(),0).right_kernel()

        component_list = []
        good_components = []
        if K.dimension() == 1:
            good_components.append((K,[]))
        else:
            component_list.append((K,[]))

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
                                    good_components.append((U0.denominator() * U0.matrix(),hecke_data+[(qq.gens_reduced()[0],Aq.restrict(U0))]))
                            else: # U0.dimension() > 2 or not is_irred
                                component_list.append((U0,hecke_data + [(qq.gens_reduced()[0],Aq.restrict(U0))]))
                    if len(good_components) > 0 and not return_all:
                        flist = []
                        for row0 in good_components[0][0].rows():
                            col0 = [ZZ(o) for o in row0.list()]
                            flist.append(sum([a * phi for a,phi in zip(col0,self.gens())],self(0)))
                        return flist,good_components[0][1]
                    if len(component_list) == 0 or num_hecke_operators >= bound:
                        break

        if len(good_components) == 0:
            raise ValueError('Group does not seem to be attached to an elliptic curve')
        else:
            if return_all:
                ans = []
                for K,hecke_data in good_components:
                    flist = []
                    for row0 in K.rows():
                        col0 = [ZZ(o) for o in row0.list()]
                        flist.append(sum([a * phi for a,phi in zip(col0,self.gens())],self(0)))
                    ans.append((flist,hecke_data))
                return ans
            else:
                flist = []
                for row0 in good_components[0][0].rows():
                    col0 = [ZZ(o) for o in row0.list()]
                    flist.append(sum([a * phi for a,phi in zip(col0,self.gens())],self(0)))
                return flist,good_components[0][1]


    def _reconstruct_from_abelianization(self,K):
        col = [ZZ(o) for o in (K.denominator()*K.matrix()).list()]
        assert len(col) % 2 == 0
        n = ZZ(len(col)/2)
        cocycle = sum([a*self.gen(i) for i,a in enumerate(col[:n]) if a != 0],self(0))
        Gab = self.group().abelianization()
        groupelement = Gab.ab_to_G(sum([a*Gab.gens()[i] for i,a in enumerate(col[n:]) if a != 0]))
        return (groupelement,cocycle)

    def get_rational_cycle_and_cocycle(self,sign = 1,use_magma = True,bound = 3, return_all = False):
        F = self.group().base_ring()
        if F.signature()[1] == 0 or (F.signature() == (0,1) and 'G' not in self.group()._grouptype):
            K1 = (self.involution_at_infinity_matrix()-sign).right_kernel()
            K2 = (self.group().involution_at_infinity_matrix_freepart()-sign).right_kernel()
        else:
            K1 = Matrix(QQ,self.dimension(),self.dimension(),0).right_kernel()
            K2 = Matrix(QQ,self.dimension(),self.dimension(),0).right_kernel()

        component_list = []
        good_components = []
        K = direct_sum_of_modules([K1,K2])
        if K.dimension() == 2:
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
            verbose('component_dimensions = %s'%([o.dimension() for o in component_list]))
            q = q.next_prime()
            for qq,e in F.ideal(q).factor():
                if  ZZ(qq.norm()).is_prime() and not qq.divides(F.ideal(disc.gens_reduced()[0])):
                    try:
                        Aq0 = self.hecke_matrix(qq.gens_reduced()[0],g0 = g0,use_magma = use_magma).change_ring(QQ)
                        Aq1 = self.group().hecke_matrix_freepart(qq.gens_reduced()[0],g0=g0,use_magma = use_magma)
                        R = Aq0.parent()
                        Aq = block_matrix([[Aq0,R(0)],[R(0),Aq1]])
                    except (RuntimeError,TypeError):
                        continue
                    verbose('Computed hecke matrix at qq = %s'%qq)
                    old_component_list = component_list
                    component_list = []
                    num_hecke_operators += 1
                    for U in old_component_list:
                        for U0,is_irred in Aq.decomposition_of_subspace(U):
                            if U0.dimension() == 2:
                                good_components.append(U0)
                            elif is_irred:
                                # Bad
                                pass
                            else: # U0.dimension() > 1 and not is_irred
                                component_list.append(U0)
                    if len(good_components) > 0 and not return_all:
                        return self._reconstruct_from_abelianization(good_components[0])
                    if len(component_list) == 0 or num_hecke_operators >= bound:
                        break

        if len(good_components) == 0:
            raise ValueError,'Group does not seem to be attached to an elliptic curve'
        else:
            if return_all:
                return [self._reconstruct_from_abelianization(K) for K in good_components]
            else:
                return self._reconstruct_from_abelianization(good_components[0])

    def apply_hecke_operator(self,c,l, hecke_reps = None,group = None,scale = 1,use_magma = True,parallelize = False,g0 = None):
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
        Gpn = self.group()
        group = Gpn
        if padic:
            prec = V.base_ring().precision_cap()
        else:
            prec = None
        vals = []
        R = V.base_ring()
        if hasattr(V,'is_full'): # This should be more robust
            Gab = Gpn.abelianization()
            gammas = [Gab.ab_to_G(o) for o in Gab.free_gens()]
        else:
            gammas = Gpn.gens()

        if self._use_ps_dists:
            S0 = self.Sigma0()
        else:
            S0 = lambda x:x
        vals = [V(0) for gamma in gammas]
        input_vector = []
        # verbose('Calculating action')
        for j,gamma in enumerate(gammas):
            input_vector.extend([(group,g,gamma,c,l,hecke_reps,padic,S0(Gpn.embed(g,prec)),self._use_ps_dists,use_magma,j) for g in hecke_reps])
        if parallelize:
            f = parallel(_calculate_hecke_contribution)
            for inp,outp in f(input_vector):
                vals[inp[0][-1]] += outp
        else:
            for inp in input_vector:
                outp = _calculate_hecke_contribution(*inp)
                vals[inp[-1]] += outp
        # verbose('Leaving apply_hecke_operator')
        return scale * self(vals)

    def get_Up_reps_local(self,prec):
        Gpn = self.group()
        if self._use_ps_dists:
            ans = [Gpn.embed(g,prec) for g in Gpn.get_Up_reps()]
        else:
            glocs = [Gpn.embed(g,prec) for g in Gpn.get_Up_reps()]
            for o in glocs:
                o.set_immutable()
            ans = [self._coeffmodule._get_powers(o) for o in glocs]
        return [set_immutable(o) for o in ans]

    def apply_Up(self,c,group = None,scale = 1,parallelize = False,times = 0,progress_bar = False,method = 'bigmatrix', repslocal = None):
        r"""
        Apply the Up Hecke operator operator to ``c``.

        EXAMPLES::

        """
        Up_reps = self.group().get_Up_reps()
        V = self.coefficient_module()
        Gpn = self.group()
        group = Gpn
        R = V.base_ring()
        if hasattr(V,'is_full'): # This should be more robust
            Gab = Gpn.abelianization()
            gammas = [Gab.ab_to_G(o) for o in Gab.free_gens()]
        else:
            gammas = Gpn.gens()

        if self._use_ps_dists:
            S0 = self.Sigma0()
        else:
            S0 = lambda x:x

        if repslocal is None:
            if not V.is_exact():
                prec = V.precision_cap()
            else:
                prec = None
            repslocal = self.get_Up_reps_local(prec)

        if method == 'naive':
            assert times == 0
            vals = [V(0) for gamma in gammas]
            input_vector = []
            for j,gamma in enumerate(gammas):
                input_vector.extend([(group,g,gamma,c,repslocal[k],self._use_ps_dists,j) for k,g in enumerate(Up_reps)])
            if parallelize:
                f = parallel(_calculate_Up_contribution)
                for inp,outp in f(input_vector):
                    vals[inp[0][-1]] += outp
            else:
                for inp in input_vector:
                    outp = _calculate_Up_contribution(*inp)
                    vals[inp[-1]] += outp
            ans = self(vals)
            if scale != 1:
                ans = scale * ans
            return ans
        else:
            assert method == 'bigmatrix'
            verbose('Getting Up matrices...')
            N = V.precision_cap()
            Up_reps = self.group().get_Up_reps()
            nreps = len(Up_reps)
            ngens = len(self.group().gens())
            S = repslocal[0].nrows()
            NN = ngens * S
            A = Matrix(ZZ,NN,NN,0)

            total_counter = ngens**2
            counter = 0
            iS = 0
            for i,gi in enumerate(self.group().gens()):
                ti = [tuple(self.group().get_Up_ti(sk,gi).word_rep) for sk in Up_reps]
                jS = 0
                for ans in find_newans(self,repslocal,ti):
                    A.set_block(iS,jS,ans)
                    jS += S
                    if progress_bar:
                        counter +=1
                        update_progress(float(counter)/float(total_counter),'Up matrix')
                iS += S
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
            bvec = Matrix(R,NN,1,[o for b in c._val for o in b._val.list()])
            if scale_factor != 1:
                bvec = scale_factor * bvec
            valmat = A * bvec
            return self([V(valmat.submatrix(row=i,nrows = N),check = False) for i in xrange(0,valmat.nrows(),N)])

def _calculate_Up_contribution(G,g,gamma,c,gloc,use_ps_dists,num_gamma):
    tig = G.get_Up_ti(g,gamma)
    if use_ps_dists:
        return gloc * c.evaluate(tig)
    else:
        ans = c.evaluate(tig,extramul = gloc)
        return ans

def _calculate_hecke_contribution(G,g,gamma,c,l,hecke_reps,padic,gloc,use_ps_dists,use_magma,num_gamma):
    tig = G.get_hecke_ti(g,gamma,l,use_magma)
    if padic:
        if use_ps_dists:
            ans = gloc *  c.evaluate(tig)
            return ans
        else:
            ans = c.evaluate(tig,extramul = gloc)
            return ans
    else:
        ans = c.evaluate(tig)
        return ans

class ShapiroImage(SageObject):
    def __init__(self,G,cocycle):
        self.G = G
        self.cocycle = cocycle

    def __call__(self,gamma):
        return CoinducedElement(self.G,self.cocycle,gamma)

class CoinducedElement(SageObject):
    def __init__(self,G,cocycle,gamma):
        self.G = G
        self.cocycle = cocycle
        self.gamma = gamma

    def __call__(self,h,check = False):
        rev, b = h
        if check:
            assert self.G.reduce_in_amalgam(b) == 1
        a = self.G.reduce_in_amalgam(b * self.gamma)
        if rev == False:
            return self.cocycle.evaluate(a)
        else:
            return -self.cocycle.evaluate(a)
