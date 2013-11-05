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
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,LaurentSeriesRing,lcm, Qp
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

oo = Infinity

def get_overconvergent_class_quaternionic(P,E,G,prec,sign_at_infinity,use_ps_dists = False,use_sage_db = False,parallelize = False):
    try:
        p = ZZ(P)
        Pnorm = p
        F = QQ
    except TypeError:
        p = ZZ(P.norm().factor()[0][0])
        Pnorm = ZZ(P.norm())
        F = P.number_field()

    if Pnorm != p:
        raise NotImplementedError,'For now I can only work over Qp'

    base_field = Qp(p,prec)

    # Define phiE, the cohomology class associated to the curve E.
    Coh = CohomologyGroup(G.small_group())
    phiE = Coh.get_cocycle_from_elliptic_curve(E,sign = sign_at_infinity)
    sgninfty = 'plus' if sign_at_infinity == 1 else 'minus'
    dist_type = 'ps' if use_ps_dists == True else 'fm'
    if hasattr(E,'cremona_label'):
        Ename = E.cremona_label()
    else:
        Ename = E.ainvs()
    fname = 'moments_%s_%s_%s_%s_%s.sobj'%(p,Ename,sgninfty,prec,dist_type)
    if use_sage_db:
        try:
            Phivals = db(fname)
            CohOC = CohomologyGroup(G.small_group(),overconvergent = True,base = base_field,use_ps_dists = use_ps_dists)
            CohOC._coeff_module = Phivals[0].parent()
            VOC = CohOC.coefficient_module()
            Phi = CohOC([VOC(o) for o in Phivals])
            return Phi
        except IOError: pass
    verbose('Computing moments...')
    CohOC = CohomologyGroup(G.small_group(),overconvergent = True,base = base_field,use_ps_dists = use_ps_dists)
    VOC = CohOC.coefficient_module()
    if use_ps_dists:
        Phi = CohOC([VOC(QQ(phiE.evaluate(g)[0])).lift(M = prec) for g in G.small_group().gens()])
    else:
        Phi = CohOC([VOC(Matrix(VOC._R,VOC._depth,1,[phiE.evaluate(g)[0]]+[0 for i in range(VOC._depth - 1)])) for g in G.small_group().gens()])
    apsign = ZZ(E.ap(p)) if E.base_ring() == QQ else ZZ(Pnorm + 1 - Curve(E.defining_polynomial().change_ring(F.residue_field(P))).count_points(1)[0])
    assert apsign.abs() == 1
    Phi = Phi.improve(prec = prec,sign = apsign,parallelize = parallelize)
    if use_sage_db:
        db_save(Phi._val,fname)
    verbose('Done.')
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
        elif parent.is_overconvergent:
            self._val = [V(data.evaluate(b)) for b in parent.group().gens()]
        elif not parent.is_overconvergent:
            self._val = [V(data.evaluate(b)) for b in parent._space.domain().basis()]

        ModuleElement.__init__(self,parent)

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

    def evaluate(self,x):
        word = tuple(self.parent().group()(x).word_rep)
        if self.parent().is_overconvergent:
            return self._evaluate_word(word)
        else:
            V = self.parent().coefficient_module()
            return sum([a*self._evaluate_at_group_generator(g) for g,a in word],V(0))

    @cached_method
    def _evaluate_at_group_generator(self,j): # j is the index in Gpn.gens()
        Gab, V0,free_idx = self.parent().group().abelianization()
        coeff_module = self.parent().coefficient_module()
        tmp = Gab(V0.gen(j))
        gablist = [tmp[i] for i in free_idx]
        assert sum(1 if a0 != 0 else 0 for a0 in gablist) <= 1
        cvals = [coeff_module(o) for o in self._val]
        val0 = sum((ZZ(a0) * b for a0,b in zip(gablist,cvals) if a0 != 0),coeff_module(0))
        return val0

    @cached_method
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
        if len(word) == 0:
            return V(0)
        # verbose('word = %s'%list(word))
        if len(word) == 1:
            g,a = word[0]
            if a == 0:
                return V(0)
            elif a == -1:
                gmat_inv = G.embed(G.gen(g).quaternion_rep**-1,prec)
                if self.parent()._use_ps_dists:
                    return -(Sigma0(gmat_inv) * self._val[g])
                else:
                    return  -self._val[g].l_act_by(gmat_inv)
            elif a < 0:
                gmat_inv = G.embed(G.gen(g).quaternion_rep**-1,prec)
                if self.parent()._use_ps_dists:
                    return -(Sigma0(gmat_inv**-a) * self._evaluate_word(tuple([(g,-a)])))
                else:
                    return -self._evaluate_word(tuple([(g,-a)])).l_act_by(gmat_inv**-a)

            elif a == 1:
                return self._val[g]
            else:
                gmat = G.embed(G.gen(g).quaternion_rep,prec)
                phig = self._val[g]
                tmp = V(phig)
                for i in range(a-1):
                    if self.parent()._use_ps_dists:
                        tmp = phig + Sigma0(gmat) * tmp
                    else:
                        tmp = phig + tmp.l_act_by(gmat)
                return tmp
        else:
            pivot = len(word) // 2
            gamma = prod([G.gen(g).quaternion_rep**a for g,a in word[:pivot]],G.B(1))
            if self.parent()._use_ps_dists:
                return self._evaluate_word(tuple(word[:pivot])) + Sigma0(G.embed(gamma,prec)) *  self._evaluate_word(tuple(word[pivot:]))
            else:
                return self._evaluate_word(tuple(word[:pivot])) +  self._evaluate_word(tuple(word[pivot:])).l_act_by(G.embed(gamma,prec))

    def improve(self,prec = None,sign = 1,parallelize = False):
        r"""
        Repeatedly applies U_p.

        EXAMPLES::

        """
        U = self.parent().coefficient_module()
        p = U.base_ring().prime()
        group = self.parent().group()
        if prec is None:
            prec = U.precision_cap()
        reps = group.get_Up_reps()
        h2 = self.parent().apply_hecke_operator(self,p, hecke_reps = reps,group = group,scale = sign,parallelize = parallelize)
        #verbose('%s'%h2,level = 2)
        verbose("Applied Up once")
        ii = 0
        current_val = min([(u-v).valuation() for u,v in zip(h2._val,self._val)])
        old_val = -oo
        while current_val < prec and current_val > old_val:
            h1 = h2
            old_val = current_val
            ii += 1
            h2 = self.parent().apply_hecke_operator(h1,p, hecke_reps = reps,group = group,scale = sign,parallelize = parallelize)
            current_val = min([(u-v).valuation() for u,v in zip(h2._val,h1._val)])
            verbose('Applied Up %s times (val = %s)'%(ii+1,current_val))
        self._val = h2._val
        verbose('Final precision of %s digits'%current_val)
        return h2

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
        else:
            self.is_overconvergent = False
            self._coeffmodule = base**1
            self._Ga,self._V,self._free_idx = G.abelianization()
            self._num_abgens = len(self._free_idx)
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
                tmp = []
                for i in self._free_idx:
                    idxlist = list(self._Ga.gen(i).lift())
                    tmp.append(sum([a*data.evaluate(t).moment(0).rational_reconstruction() for a,t in zip(idxlist,gens)]))
                return self.element_class(self,tmp)
            else:
                return self.element_class(self,[V(data.evaluate(g)) for g in G.gens()])
        else:
            return self.element_class(self,[self._coeffmodule(data) for g in range(self._num_abgens)])

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
    def hecke_matrix(self,l):
        if self.coefficient_module().dimension() > 1:
            raise NotImplementedError
        dim = self.dimension()
        R = self.coefficient_module().base_ring()
        M = matrix(R,dim,dim,0)
        for j,cocycle in enumerate(self.gens()):
            # Construct column j of the matrix
            M.set_column(j,[o[0] for o in self.apply_hecke_operator(cocycle,l).values()])
        return M

    @cached_method
    def involution_at_infinity_matrix(self):
        if self.coefficient_module().dimension() > 1:
            raise NotImplementedError
        H = self._space
        Gpn = self.group()
        x = Gpn.element_of_norm(-1)
        dim = self.dimension()
        M = matrix(QQ,dim,dim,0)
        for j,c in enumerate(self.gens()):
            # Construct column j of the matrix
            for i in range(dim):
                ti = Gpn(x**-1 * prod([Gpn.gen(idx)**a for idx,a in zip(range(len(Gpn.gens())),list(self._Ga.gen(self._free_idx[i]).lift()))]).quaternion_rep * x)
                M[i,j] = c.evaluate(ti)[0]
        return M

    def get_cocycle_from_elliptic_curve(self,E,sign = 1):
        K = (self.involution_at_infinity_matrix()-sign).right_kernel()
        discnorm = self.group()._O_discriminant.norm()
        F = self.group().base_ring()
        try:
            N = ZZ(discnorm.gen())
        except AttributeError:
            N = ZZ(discnorm)

        q = ZZ(1)
        while K.dimension() != 1:
            q = q.next_prime()
            if N % q == 0:
                continue
            if F == QQ:
                Eap = E.ap(q)
            else:
                Q = F(q).factor()[0][0]
                Eap = ZZ(Q.norm() + 1 - E.reduction(Q).count_points())

            K1 = (self.hecke_matrix(q)-Eap).right_kernel()
            K = K.intersection(K1)
        col = [ZZ(o) for o in (K.denominator()*K.matrix()).list()]
        return sum([a*self.gen(i) for i,a in enumerate(col) if a != 0],self(0))

    def apply_hecke_operator(self,c,l, hecke_reps = None,group = None,scale = 1,parallelize = False):
        r"""
        Apply the l-th Hecke operator operator to ``c``.

        EXAMPLES::

        """
        if hecke_reps is None:
            hecke_reps = self.group().get_hecke_reps(l) # Assume l != p here!
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
            gammas = []
            Gab,Vmod,free_idx = Gpn.abelianization()
            for i in free_idx:
                idxlist = list(Gab.gen(i).lift())
                gammas.append(prod([t**a for a,t in zip(idxlist,Gpn.gens()) if a != 0]))
        else:
            gammas = Gpn.gens()

        if self._use_ps_dists:
            S0 = self.Sigma0()
        else:
            S0 = lambda x:x
        vals = [V(0) for gamma in gammas]
        input_vector = []
        for j,gamma in enumerate(gammas):
            input_vector.extend([(group,g,gamma.quaternion_rep,c,l,hecke_reps,padic,S0(Gpn.embed(g,prec)),self._use_ps_dists,j) for g in hecke_reps])
        if parallelize:
            f = parallel(_calculate_hecke_contribution)
            for inp,outp in f(input_vector):
                vals[inp[0][-1]] += outp
        else:
            for inp in input_vector:
                outp = _calculate_hecke_contribution(*inp)
                vals[inp[-1]] += outp #_calculate_hecke_contribution(group,g,gamma.quaternion_rep,c,l,hecke_reps,padic,S0(Gpn.embed(g,prec)),self._use_ps_dists)
        return scale * self(vals)

def _calculate_hecke_contribution(G,g,gamma,c,l,hecke_reps,padic,gloc,use_ps_dists,num_gamma = 0):
    tig = G.get_hecke_ti(g,gamma,l,reps = hecke_reps)
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
