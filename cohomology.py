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
from util import *
import os
from ocmodule import OCVn
from sage.misc.persist import db,db_save
from sage.schemes.plane_curves.constructor import Curve
from sage.parallel.decorate import fork,parallel
from sage.parallel.ncpus import ncpus
oo = Infinity
from sage.matrix.constructor import block_matrix
from sage.rings.number_field.number_field import NumberField
load('fmpz_mat.spyx')

def take_super_power(a,n,N):
    R = a.parent().base_ring()
    aflint = Fmpz_mat(a)
    for i in range(n):
        aflint.square_inplace()
        if N != 0:
            aflint.modreduce(N)
        update_progress(float(i+1)/float(n),'Exponentiating matrix')
    return aflint._sage_()

def get_overconvergent_class_quaternionic(P,E,G,prec,sign_at_infinity,use_ps_dists = False,use_sage_db = False,parallelize = False,apsign = None,progress_bar = False,method = None,phiE = None):
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
            raise ValueError,'method shouldbe either "naive" or "bigmatrix"'
    if Pnorm != p:
        raise NotImplementedError,'For now I can only work over totally split'

    base_ring = Zp(p,prec) #Qp(p,prec)

    # Define phiE, the cohomology class associated to the curve E.

    if phiE is None:
        phiE = CohomologyGroup(G.small_group()).get_cocycle_from_elliptic_curve(E,sign = sign_at_infinity)

    sgninfty = 'plus' if sign_at_infinity == 1 else 'minus'
    dist_type = 'ps' if use_ps_dists == True else 'fm'
    if hasattr(E,'cremona_label'):
        Ename = E.cremona_label()
    elif hasattr(E,'ainvs'):
        Ename = E.ainvs()
    else:
        Ename = 'unknown'
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
        Phi = CohOC([VOC(Matrix(VOC._R,VOC._depth,1,[phiE.evaluate(g)[0]]+[0 for i in range(VOC._depth - 1)])) for g in G.small_group().gens()])
    if apsign is None:
        apsign = ZZ(E.ap(p)) if F == QQ else ZZ(Pnorm + 1 - Curve(E.defining_polynomial().change_ring(F.residue_field(P))).count_points(1)[0])
    assert apsign.abs() == 1
    if progress_bar:
        verb_level = get_verbose()
        # set_verbose(0)
    Phi = Phi.improve(prec = prec,sign = apsign,parallelize = parallelize,progress_bar = progress_bar,method = method)
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

    def evaluate_oc(self,x,parallelize = False,extramul = None):
        H = self.parent()
        if H._use_ps_dists:
            return self.evaluate_oc_naive(x,extramul = extramul)
        G = H.group()
        V = H.coefficient_module()
        prec = V.base_ring().precision_cap()
        Sigma0 = H.Sigma0()
        if hasattr(x,'word_rep'):
            wd  = x.word_rep
        else:
            x = G(x)
            wd = x.word_rep
        if len(wd) == 0:
            return V(0)
        emb = lambda x:G.embed(x,prec)
        W = self._val[0]._val.parent()
        i,a = wd[-1]
        ans = H.get_fox_term(i,a) * self.get_flint_val(i)
        ans.modreduce(H._pN)
        for i,a in reversed(wd[:-1]):
            ans = H.get_fox_term(i,a) * self.get_flint_val(i) + H.get_gen_pow(i,a) * ans
            ans.modreduce(H._pN)
        if extramul is not None:
            ans = extramul * ans
            ans.modreduce(H._pN)
        ans = V(ans._sage_())
        return ans

    @cached_method
    def get_flint_val(self,i):
        return Fmpz_mat(self._val[i]._val)

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
        return sum([ZZ(a0) * b for a0,b in zip(gablist,cvals) if a0 != 0],coeff_module(0))

    def _evaluate_syllable(self,g,a):
        G = self.parent().group()
        V = self.parent().coefficient_module()
        prec = V.base_ring().precision_cap()
        Sigma0 = self.parent().Sigma0()
        #G._evaluate_stats[ZZ(a).abs()] += 1
        if a == 1:
            return self._val[g]
        elif a == 0:
            return V(0)
        elif a == -1:
            # gmat_inv = G.embed(G.gen(g).quaternion_rep**-1,prec)
            gmat_inv = G.gen(g).embed(prec).adjoint() # G.gen(g).embed(prec)**-1
            if self.parent()._use_ps_dists:
                return -(Sigma0(gmat_inv) * self._val[g])
            else:
                return  -self._val[g].l_act_by(gmat_inv)
        elif a < 0:
            gmat = G.gen(g).embed(prec) # G.embed(G.gen(g).quaternion_rep,prec)
            gmat_inv = gmat.adjoint() #gmat**-1
            phig = self._val[g]
            tmp = V(phig)
            if self.parent()._use_ps_dists:
                for i in range(-a-1):
                    tmp = phig + Sigma0(gmat) * tmp
                return -(Sigma0(gmat_inv**-a) * tmp)
            else:
                for i in range(-a-1):
                    tmp = phig + tmp.l_act_by(gmat)
                return -(tmp.l_act_by(gmat_inv**-a))
        else:
            gmat = G.gen(g).embed(prec) #G.embed(G.gen(g).quaternion_rep,prec)
            phig = self._val[g]
            tmp = V(phig)
            if self.parent()._use_ps_dists:
                for i in range(a-1):
                    tmp = phig + Sigma0(gmat) * tmp
            else:
                for i in range(a-1):
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
        prec = V.base_ring().precision_cap()
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

    def improve(self,prec = None,sign = 1,parallelize = False,progress_bar = False,method = 'bigmatrix'):
        r"""
        Repeatedly applies U_p.

        EXAMPLES::

        """
        U = self.parent().coefficient_module()
        p = U.base_ring().prime()
        group = self.parent().group()
        if prec is None:
            prec = U.precision_cap()
        # reps = group.get_Up_reps()
        if method == 'naive':
            repslocal = self.get_Up_reps_local(prec)
            h2 = self.parent().apply_Up(self, group = group,scale = sign,parallelize = parallelize,method = 'naive',repslocal = repslocal)
            if progress_bar:
                update_progress(1.0/float(prec),'f|Up')
            else:
                verbose("Applied Up once")
            ii = 0
            current_val = min([(u-v).valuation() for u,v in zip(h2._val,self._val)])
            old_val = -oo
            while current_val < prec and current_val > old_val:
                h1 = h2
                old_val = current_val
                ii += 1
                h2 = self.parent().apply_Up(h1,group = group,scale = sign,parallelize = parallelize,method = 'naive',repslocal = repslocal)
                current_val = min([(u-v).valuation() for u,v in zip(h2._val,h1._val)])
                if progress_bar:
                    update_progress(float(ii+1)/float(prec),'f|Up')
                else:
                    verbose('Applied Up %s times (val = %s)'%(ii+1,current_val))
            self._val = h2._val
            # verbose('Final precision of %s digits'%current_val)
            return h2
        else:
            assert method == 'bigmatrix'
            return self.parent().apply_Up(self, group = group,scale = sign,parallelize = parallelize,times = len(ZZ(prec-1).bits()),progress_bar = progress_bar,method = method)


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
                self._coeffmodule = OCVn(0,base,1+base.precision_cap())
            self._num_abgens = len(self._group.gens())
            self._gen_pows = []
            self._gen_pows_neg = []
            for i,g in enumerate(self._group.gens()):
                gmat = self.group().embed(self._group.Ugens[i],1+base.precision_cap())
                gmat.set_immutable()
                A = Fmpz_mat(self._coeffmodule._get_powers(gmat))
                self._gen_pows.append([A.identitymatrix(),A])
                gmatinv = gmat**-1
                gmatinv.set_immutable()
                Ainv = Fmpz_mat(self._coeffmodule._get_powers(gmatinv))
                self._gen_pows_neg.append([A.identitymatrix(),Ainv])

            self._pN = self._coeffmodule.base_ring().prime()**base.precision_cap()

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
            return self.element_class(self,[self._coeffmodule(data) for g in range(self._num_abgens)])

    # @cached_method
    def fox_gradient(self,word):
        h = self.get_gen_pow(0,0)
        ans = [h.zeromatrix() for o in self.group().gens()]
        if len(word) == 0:
            return ans
        lenword = len(word)
        for j in range(lenword):
            i,a = word[j]
            ans[i] += h  * self.get_fox_term(i,a)
            if j < lenword -1:
                h = h * self.get_gen_pow(i,a)
                h.modreduce(self._pN)
        for o in ans:
            o.modreduce(self._pN)
        return ans

    def get_gen_pow(self,i,a):
        if a == 0:
            return self._gen_pows[0][0]
        elif a > 0:
            genpows = self._gen_pows[i]
            while len(genpows) <= a:
                genpows.append(genpows[1] * genpows[-1])
                genpows[-1].modreduce(self._pN)
            return genpows[a]
        else:
            genpows = self._gen_pows_neg[i]
            while len(genpows) <= -a:
                genpows.append(genpows[1] * genpows[-1])
                genpows[-1].modreduce(self._pN)
            return genpows[-a]

    @cached_method
    def get_fox_term(self,i,a):
        if a >= 0:
            self.get_gen_pow(i,a-1)
            return (reduce(lambda x,y:x+y,[self._gen_pows[i][o] for o in range(a)]))#.change_ring(self.coefficient_module().base_ring())
        else:
            self.get_gen_pow(i,a)
            return (-reduce(lambda x,y:x+y,[self._gen_pows_neg[i][o] for o in range(1,-a+1)]))#.change_ring(self.coefficient_module().base_ring())


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
        return [self.gen(i) for i in range(self.dimension())]

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
            g = Gpn(x**-1 * Gab.ab_to_G(g0).quaternion_rep * x)
            M.set_column(j,list(Gab.G_to_ab_free(g)))
        return M.transpose()

    def get_cocycle_from_elliptic_curve(self,E = None,sign = 1,use_magma = False):
        F = self.group().base_ring()
        if F.signature()[0] == 0 or 'G' in self.group()._grouptype:
            K = Matrix(QQ,self.dimension(),self.dimension(),0).right_kernel()
        else:
            K = (self.involution_at_infinity_matrix()-sign).right_kernel()

        disc = self.group()._O_discriminant
        discnorm = disc.norm()
        try:
            N = ZZ(discnorm.gen())
        except AttributeError:
            N = ZZ(discnorm)

        if hasattr(E,'conductor'):
            def getap(q):
                if F == QQ:
                    return E.ap(q)
                else:
                    Q = F.ideal(q).factor()[0][0]
                    return ZZ(Q.norm() + 1 - E.reduction(Q).count_points())
        elif E is not None:
            def getap(q):
                return E(q)
        else:
            getap = None

        if F == QQ:
            x = QQ['x'].gen()
            F = NumberField(x,names='a')
        q = ZZ(1)
        g0 = None
        while K.dimension() > 1:
            q = q.next_prime()
            for qq,e in F.ideal(q).factor():
            # for g0 in self.group().element_of_prime_norm(1000):
                # qq = g0.reduced_norm()
                if  ZZ(qq.norm()).is_prime() and not qq.divides(F.ideal(disc.gens_reduced()[0])):
                    if getap is not None:
                        try:
                            ap = getap(qq)
                        except (ValueError,ArithmeticError):
                            continue
                    else:
                        ap = self.hecke_matrix(qq.gens_reduced()[0],g0 = g0).eigenvalues(extend = False)[0]
                        verbose('Found aq = %s'%ap)
                    K1 = (self.hecke_matrix(qq.gens_reduced()[0],g0 = g0)-ap).right_kernel()
                    K = K.intersection(K1)
        assert K.dimension() == 1
        col = [ZZ(o) for o in (K.denominator()*K.matrix()).list()]
        return sum([a*self.gen(i) for i,a in enumerate(col) if a != 0],self(0))

    def apply_hecke_operator(self,c,l, hecke_reps = None,group = None,scale = 1,use_magma = True,parallelize = False,g0 = None):
        r"""
        Apply the l-th Hecke operator operator to ``c``.

        EXAMPLES::

        """
        if hecke_reps is None:
            hecke_reps = self.group().get_hecke_reps(l,use_magma = use_magma) # Assume l != p here!
            # if self.group().O.discriminant() % l == 0:
            #     hecke_reps = self.group().get_Up_reps()
            # else:
            #     hecke_reps = self.group().get_hecke_reps(l)

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
        for j,gamma in enumerate(gammas):
            input_vector.extend([(group,g,gamma.quaternion_rep,c,l,hecke_reps,padic,S0(Gpn.embed(g,prec)),self._use_ps_dists,j,use_magma) for g in hecke_reps])
        if parallelize:
            f = parallel(_calculate_hecke_contribution)
            for inp,outp in f(input_vector):
                vals[inp[0][-1]] += outp
        else:
            for inp in input_vector:
                outp = _calculate_hecke_contribution(*inp)
                vals[inp[-1]] += outp
        return scale * self(vals)

    def get_Up_reps_local(self,prec):
        Gpn = self.group()
        if self._use_ps_dists:
            return [Gpn.embed(g,prec) for g in Gpn.get_Up_reps()]
        else:
            glocs = [Gpn.embed(g,prec) for g in Gpn.get_Up_reps()]
            for o in glocs:
                o.set_immutable()
            return [self._coeffmodule._get_powers(o) for o in glocs]

    def get_Up_matrix(self,prec,progress_bar = False):
        r'''
        Return a block matrix W such that:
        W[i,j] = \sum_k s_k \frac{\partial t_k(g_i)}{\partial g_j}

        This allows one to compute the Up action as:
        c_i <- \sum_j W[i,j] * c_j
        '''
        verbose('Getting Up matrices...')
        V = self.coefficient_module()
        R = V.base_ring()
        N = V.precision_cap()
        Gpn = self.group()
        Up_reps = Gpn.get_Up_reps()
        ngens = len(Gpn.gens())
        nreps = len(Up_reps)
        glocs = [Fmpz_mat(o) for o in self.get_Up_reps_local(prec)]
        ans = [[None for u in Gpn.gens()] for o in Gpn.gens()]
        total_counter = ngens*(nreps+ngens)
        counter = 0
        for i,gi in enumerate(Gpn.gens()):
            giquat = gi.quaternion_rep
            fox_gradients = []
            for k,sk in enumerate(Up_reps):
                fox_gradients.append(self.fox_gradient(tuple(Gpn.get_Up_ti(sk,giquat).word_rep)))
                if progress_bar:
                    counter +=1
                    update_progress(float(counter)/float(total_counter),'Up matrix')

            for j,gj in enumerate(Gpn.gens()):
                ansij = sum([glocs[k] * fox_gradients[k][j] for k in range(nreps)],glocs[0].zeromatrix())
                ansij.modreduce(self._pN)
                ans[i][j] = ansij #._sage_()
                if progress_bar:
                    counter +=1
                    update_progress(float(counter)/float(total_counter),'Up matrix')
        verbose('Translating to Sage')
        for i in range(ngens):
            for j in range(ngens):
                ans[i][j] = ans[i][j]._sage_()
        verbose('Done translating to Sage')
        return block_matrix(ans)

    def apply_Up(self,c,group = None,scale = 1,parallelize = False,times = 0,progress_bar = False,method = 'bigmatrix', repslocal = None):
        r"""
        Apply the Up Hecke operator operator to ``c``.

        EXAMPLES::

        """
        Up_reps = self.group().get_Up_reps()
        V = self.coefficient_module()
        padic = not V.base_ring().is_exact()
        Gpn = self.group()
        group = Gpn
        if padic:
            prec = V.base_ring().precision_cap()
        else:
            prec = None
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

        if method == 'naive':
            assert times == 0
            vals = [V(0) for gamma in gammas]
            if repslocal is None:
                glocs = self.get_Up_reps_local(prec)
            input_vector = []
            for j,gamma in enumerate(gammas):
                if self._use_ps_dists:
                    input_vector.extend([(group,g,gamma.quaternion_rep,c,glocs[k],self._use_ps_dists,j) for k,g in enumerate(Up_reps)])
                else:
                    input_vector.extend([(group,g,gamma.quaternion_rep,c,glocs[k],self._use_ps_dists,j) for k,g in enumerate(Up_reps)])
            if parallelize:
                f = parallel(_calculate_Up_contribution)
                for inp,outp in f(input_vector):
                    vals[inp[0][-1]] += outp
            else:
                for inp in input_vector:
                    outp = _calculate_Up_contribution(*inp)
                    vals[inp[-1]] += outp
            return scale * self(vals)
        else:
            assert method == 'bigmatrix'
            A = scale * self.get_Up_matrix(prec,progress_bar = progress_bar)
            if times != 0:
                verbose('Computing 2^(%s)-th power of a %s x %s matrix'%(times,A.nrows(),A.ncols()))
                A = take_super_power(A,times,self._pN)
                verbose('Done computing 2^(%s)-th power'%times)
            valvec = [o for b in c._val for o in b._val.list() ]
            valmat = A * Matrix(R,A.nrows(),1, valvec)
            depth = V.precision_cap()
            assert len(valvec) == A.nrows()
            assert depth * len(Gpn.gens()) == A.nrows()
            return self([V(valmat.submatrix(row=i,nrows = depth)) for i in range(0,A.nrows(),depth)])


def _calculate_Up_contribution(G,g,gamma,c,gloc,use_ps_dists,num_gamma):
    tig = G.get_Up_ti(g,gamma)
    if use_ps_dists:
        return gloc * c.evaluate(tig)
    else:
        return c.evaluate(tig,extramul = gloc)

def _calculate_hecke_contribution(G,g,gamma,c,l,hecke_reps,padic,gloc,use_ps_dists,num_gamma,use_magma):
    tig = G.get_hecke_ti(g,gamma,l,use_magma)
    val0 = c.evaluate(tig)
    if padic:
        if use_ps_dists:
            return gloc * val0
        else:
            return val0.l_act_by(gloc)
    else:
        return val0

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
