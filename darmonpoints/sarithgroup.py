######################
##                  ##
##    QUATERNIONIC  ##
##    ARITHMETIC    ##
##    GROUP         ##
##                  ##
######################
from sage.structure.sage_object import SageObject
from sage.misc.all import cached_method,lazy_attribute,walltime
from sage.groups.group import AlgebraicGroup
from sage.structure.element import MultiplicativeGroupElement
from sage.structure.parent import Parent
from sage.algebras.quatalg.all import QuaternionAlgebra
from sage.matrix.all import matrix,Matrix
from sage.modules.all import vector
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,NumberField,QQ,ZZ,Qp,Zmod
from sage.functions.trig import arctan
from sage.misc.misc_c import prod
from sage.structure.sage_object import save,load
from sage.misc.persist import db
from sage.modules.free_module import FreeModule_generic
from sage.modular.arithgroup.congroup_gamma0 import Gamma0_constructor as Gamma0
from sage.modular.cusps import Cusp

from collections import defaultdict
from itertools import product,chain,groupby,islice,tee,starmap
import os,datetime

from .arithgroup import ArithGroup_nf_fuchsian, ArithGroup_nf_kleinian,ArithGroup_rationalquaternion,ArithGroup_rationalmatrix,ArithGroup_nf_matrix, ArithGroup_nf_matrix_new
from .homology_abstract import ArithHomology, HomologyGroup
from .util import *

class BTEdge(SageObject):
    r'''
    A BTEdge is represented by an element `gamma`, and then a flag called `reverse`.
    The flag reverse indicates whether we refer to the opposite edge of the one
    represented by `gamma`.
    '''
    def __init__(self,reverse,gamma):
        self.reverse = reverse
        self.gamma = gamma
        set_immutable(self.gamma)

    def _repr_(self):
        return "(%s)^%s"%(self.gamma,'+' if self.reverse == False else '-')

    def __iter__(self):
        return iter([self.reverse,self.gamma])

def attach_kleinian_code(magma):
    page_path = os.path.dirname(__file__) + '/KleinianGroups-1.0/klngpspec'
    magma.attach_spec(page_path)
    magma.eval('Page_initialized := true')
    return

def is_page_initialized(magma):
    try:
        return magma.eval('Page_initialized') == 'true'
    except RuntimeError:
        return False

def BigArithGroup(p, quat_data, level, base = None, grouptype = None, seed = None, use_sage_db = False, magma = None, logfile = None, **kwargs):
    if magma is None:
        from sage.interfaces.magma import Magma
        magma = Magma(logfile = logfile)
    if seed is not None:
        magma.eval('SetSeed(%s)'%seed)
    if not is_page_initialized(magma):
        attach_kleinian_code(magma)
    a, b = None, None
    if logfile is not None:
        magma.eval('SetVerbose("Kleinian",2)')
    try:
        discriminant = ZZ(quat_data)
        if base is not None:
            assert base == QQ
        else:
            base = QQ
        fname = 'arithgroup%s_%s_%s_%s.sobj'%(seed,p,discriminant,level) # Fix this name
    except TypeError:
        a,b = quat_data
        if base is None:
            base = a.parent()
        discriminant = QuaternionAlgebra(base,a,b).discriminant()
        fname = 'arithgroup%s_%s_%s_%s.sobj'%(seed,p,discriminant,level) # Fix this name
    if base != QQ:
        use_sage_db = False # This is not implemented yet

    if grouptype is None:
        if base == QQ:
            grouptype = 'PSL2'
        else:
            grouptype = 'PSL2' # DEBUG, was PGL2

    if use_sage_db:
        try:
            newobj = db(fname)
        except IOError:
            verbose('Group not found in database. Computing from scratch.')
            newobj = BigArithGroup_class(base,p,discriminant,level,seed,grouptype = grouptype,magma = magma, **kwargs)
            newobj.save_to_db()
    else:
        if a is not None:
            newobj = BigArithGroup_class(base,p,discriminant,abtuple = (a,b),level = level,seed = seed,grouptype = grouptype,magma = magma, **kwargs)
        else:
            newobj = BigArithGroup_class(base,p,discriminant,level = level,seed = seed,grouptype = grouptype,magma = magma, **kwargs)
    return newobj


class BigArithGroup_class(AlgebraicGroup):
    r'''
    This class holds information about the group `\Gamma`: a finite
    presentation for it, a solution to the word problem,...

    Initializes the group attached to a `\ZZ[1/p]`-order of the rational quaternion algebra of
    discriminant `discriminant` and  level `n`.

    TESTS:

        sage: from darmonpoints.sarithgroup import BigArithGroup
        sage: GS = BigArithGroup(7,6,1,outfile='/tmp/darmonpoints.tmp',use_shapiro=False) #  optional - magma
        sage: G = GS.small_group() #  optional - magma
        sage: a = G([2,2,1,1,1,-3]) #  optional - magma
        sage: b = G([2,2,2])    #  optional - magma
        sage: c = G([3])        #  optional - magma
        sage: print(a * b) # random #  optional - magma
        -236836769/2 + 120098645/2*i - 80061609/2*j - 80063439/2*k
        sage: b.quaternion_rep # random #  optional - magma
        846 - 429*i + 286*j + 286*k
    '''
    def __init__(self, base, p, discriminant, abtuple = None, level = 1, outfile = None, magma = None, character = None, **kwargs):
        seed = kwargs.get('seed', None)
        self.seed = seed
        self.magma = magma
        self._use_shapiro = kwargs.get('use_shapiro', False)
        self._hardcode_matrices = kwargs.get('hardcode_matrices', ((abtuple is None and discriminant == 1) or abtuple == (1,1)))
        nscartan = kwargs.get('nscartan', None)
        if seed is not None:
            verbose('Setting Magma seed to %s'%seed)
            self.magma.eval('SetSeed(%s)'%seed)
        self.F = base
        if self.F != QQ:
            Fideal = self.F.maximal_order().ideal
            self.ideal_p = Fideal(p)
            self.norm_p = ZZ(p.norm())
            self.discriminant = Fideal(discriminant)
            self.level = Fideal(level)
        else:
            self.ideal_p = ZZ(p)
            self.norm_p = ZZ(p)
            self.discriminant = ZZ(discriminant)
            self.level = ZZ(level)

        if nscartan is not None:
            self.level *= nscartan

        if self._hardcode_matrices:
            assert abtuple is None and self.discriminant == 1 or abtuple == (1,1)

        self.p = self.norm_p.prime_divisors()[0]
        if not self.ideal_p.is_prime():
            raise ValueError('p (=%s) must be prime'%self.p)

        if self._use_shapiro:
            covol = covolume(self.F,self.discriminant,self.level)
        else:
            covol = covolume(self.F,self.discriminant,self.ideal_p * self.level)
        verbose('Estimated Covolume = %s'%covol)
        difficulty = covol**2
        verbose('Estimated Difficulty = %s'%difficulty)
        verbose('Initializing arithmetic group G(pn)...')
        t = walltime()
        lev = self.ideal_p * self.level
        if character is not None:
            lev = [lev, character]
        self.Gpn = ArithGroup(self.F,self.discriminant,abtuple,lev,magma = magma, compute_presentation = not self._use_shapiro, **kwargs)
        self.Gpn.get_embedding = self.get_embedding
        self.Gpn.embed = self.embed
        verbose('Initializing arithmetic group G(n)...')
        lev = self.level
        if character is not None:
            lev = [lev, character]
        self.Gn = ArithGroup(self.F,self.discriminant,abtuple,lev,info_magma = self.Gpn,magma = magma, compute_presentation = True, **kwargs)
        t = walltime(t)
        verbose('Time for calculation T = %s'%t)
        verbose('T = %s x difficulty'%RealField(25)(t/difficulty))

        self.Gn.get_embedding = self.get_embedding
        self.Gn.embed = self.embed
        if hasattr(self.Gpn.B,'is_division_algebra'):
            fwrite('# B = F<i,j,k>, with i^2 = %s and j^2 = %s'%(self.Gpn.B.gens()[0]**2,self.Gpn.B.gens()[1]**2),outfile)
            fwrite('# disc(B) = %s'%self.Gpn.B.discriminant(), outfile)
        else:
            fwrite('# B = M_2(F)',outfile)
        try:
            basis_data_1 = list(self.Gn.Obasis)
            if not self.use_shapiro():
                basis_data_p = list(self.Gpn.Obasis)
        except AttributeError:
            try:
                basis_data_1 = self.Gn._get_basis_invmat().inverse().columns()
                if not self.use_shapiro():
                    basis_data_p = self.Gpn._get_basis_invmat().inverse().columns()
            except AttributeError:
                basis_data_1 = '?'
                basis_data_p = '?'
        self._prec = -1
        self.get_embedding(2000)
        fwrite('# R with basis %s'%basis_data_1,outfile)
        self.Gn.get_Up_reps = self.get_Up_reps
        if not self.use_shapiro():
            fwrite('# R(p) with basis %s'%basis_data_p,outfile)
            self.Gpn.get_Up_reps = self.get_Up_reps
        self.Gn.wp = self.wp
        self.Gpn.wp = self.wp
        verbose('Done initializing arithmetic groups')
        verbose('Done initialization of BigArithmeticGroup')

    def base_field(self):
        return self.F

    def quaternion_algebra(self):
        return self.B

    def clear_cache(self):
        self.Gn.clear_cache()
        if not self.use_shapiro():
            self.Gpn.clear_cache()

    def _repr_(self):
       return 'S-Arithmetic Rational Group attached to data p = %s,  disc = %s, level = %s'%(self.p,self.discriminant,self.level)

    def prime(self):
        return self.p

    def use_shapiro(self):
        return self._use_shapiro

    def base_ring_local_embedding(self, prec = None):
        if self.F == QQ:
            if prec is not None:
                return self.F.hom([Qp(self.p, prec)(1)], check=False)
            else:
                return self.F.Hom(self.F).identity()
        else:
            self.local_splitting(prec)
            if hasattr(self.Gpn,'_F_to_local'):
                self.Gn._F_to_local = self.Gpn._F_to_local
                return self.Gpn._F_to_local
            else:
                self.Gpn._F_to_local = self.Gn._F_to_local
                return self.Gn._F_to_local

    def local_splitting(self,prec):
        r"""
        Finds an embedding of the definite quaternion algebra
        into the algebra of 2x2 matrices with coefficients in `\QQ_p`.

        INPUT:

        - prec -- Integer. The precision of the splitting.

        OUTPUT:

        - Matrices I, J, K giving the splitting.

        EXAMPLES::

            sage: from darmonpoints.sarithgroup import BigArithGroup
            sage: X = BigArithGroup(13,2*3,1,outfile='/tmp/darmonpoints.tmp') #  optional - magma
            sage: II, JJ, KK = X.local_splitting(10) #  optional - magma
            sage: B = X.Gn.B    #  optional - magma
            sage: II**2 == QQ(B.gen(0)**2) #  optional - magma
            True

        """
        if prec is None or prec <= self._prec:
            try:
                return self.Gpn._II,self.Gpn._JJ,self.Gpn._KK
            except AttributeError:
                pass
        return self.Gpn._compute_padic_splitting(self.ideal_p, prec)

    def save_to_db(self):
        fname = 'arithgroup%s_%s_%s_%s.sobj'%(self.seed,self.p,self.discriminant,self.level)
        self.db(fname)

    def small_group(self):
        return self.Gpn

    def large_group(self):
        return self.Gn

    def is_in_Gpn_order(self, x):
        return self.Gpn._is_in_order(x)

    def Gpn_Obasis(self):
        return self.Gpn._get_O_basis()

    def Gpn_denominator(self, x):
        return self.Gpn._denominator(x)

    @cached_method
    def get_BT_reps(self):
        reps = [self.Gpn.B(1)] + [None for i in range(self.p)]
        emb = self.get_embedding(20)
        matrices = [(i+1,matrix(QQ,2,2,[i,1,-1,0])) for i in range(self.p)]
        if self._hardcode_matrices: # DEBUG
            verbose('Using hard-coded matrices for BT (Bianchi)')
            if self.F == QQ:
                alist = range(self.prime())
                pi = self.prime()
            else:
                alist = self.ideal_p.residues()
                pi = self.ideal_p.gens_reduced()[0]
            wp = self.wp()
            return [self.Gpn(1).quaternion_rep] + [1 / self.prime() * wp * self.Gn.matrix_to_quaternion(matrix(self.F,2,2,[1,-a,0,self.prime()])) for a in alist]

        # BTreps0 = [ Matrix(self.F,2,2,[0, -1, 1, -i]) for i in self.ideal_p.residues() ]
        # BTreps = [self.Gn(1).quaternion_rep] + [self.Gn.matrix_to_quaternion(o) for o in BTreps0]
        # return BTreps

        for n_iters,elt in enumerate(self.Gn.enumerate_elements()):
            new_inv = elt**(-1)
            embelt = emb(elt)
            if (embelt[0,0]-1).valuation() > 0 and all([not self.is_in_Gpn_order(o * new_inv) for o in reps if o is not None]):
                if hasattr(self.Gpn,'nebentypus'):
                    tmp = self.do_tilde(embelt)**-1
                    tmp = tmp[0,0] / (self.p**tmp[0,0].valuation())
                    tmp = ZZ(tmp.lift()) % self.Gpn.level
                    if tmp not in self.Gpn.nebentypus:
                        continue
                for idx,o1 in enumerate(matrices):
                    i,mat = o1
                    if is_in_Gamma0loc(embelt * mat, det_condition = False):
                        reps[i] = set_immutable(elt)
                        del matrices[idx]
                        verbose('%s, len = %s/%s'%(n_iters,self.p+1-len(matrices),self.p+1))
                        if len(matrices) == 0:
                            return reps
                        break

    def do_tilde(self, g, wp = None):
        if wp is None:
            wp = self.wp()
        if self.F == QQ and self.discriminant == 1:
            lam = -wp.determinant()
        else:
            lam = -wp.reduced_norm()
        ans = 1/lam * wp * g * wp
        set_immutable(ans)
        return ans

    @cached_method
    def get_BT_reps_twisted(self):
        ans = [self.Gn.B(1)] + [self.do_tilde(g) for g in self.get_BT_reps()[1:]]
        for o in ans:
            set_immutable(o)
        return ans

    @cached_method
    def get_Up_reps(self):
        if self._hardcode_matrices:
            B = self.small_group().B
            try:
                pi = self.ideal_p.gens_reduced()[0]
                pinorm = pi.norm()
                alist = list(self.ideal_p.residues())
            except AttributeError:
                pi = self.prime()
                pinorm = pi
                alist = [a for a in range(pinorm)]

            Upreps0 = [ Matrix(self.F,2,2,[pi, a, 0, 1]) for a in alist ]
            Upreps = [self.small_group().matrix_to_quaternion(o) for o in Upreps0]
            for o in Upreps:
                set_immutable(o)
            return Upreps

        wp = self.wp()
        if self.F == QQ and self.discriminant == 1:
            lam = -wp.determinant()
        else:
            lam = -wp.reduced_norm()
        tmp = [ lam * o**-1 * wp**-1 for o in self.get_BT_reps()[1:]]
        for o in tmp:
            set_immutable(o)
        return tmp

    @cached_method
    def get_Up_reps_bianchi(self, pi, pi_bar):
        if not self._hardcode_matrices:
            raise NotImplementedError('For Bianchi, need to hardcode matrices')
        B = self.small_group().B
        # alist = range(self.prime())
        alist = list(self.ideal_p.residues())
        Upreps0 = [ Matrix(self.F,2,2,[pi, a, 0, 1]) for a in alist ]
        Upreps_bar0 = [ Matrix(self.F,2,2,[pi_bar, a, 0, 1]) for a in alist ]
        Upreps = [self.small_group().matrix_to_quaternion(o) for o in Upreps0]
        Upreps_bar = [self.small_group().matrix_to_quaternion(o) for o in Upreps_bar0]
        for o in Upreps:
            set_immutable(o)
        for o in Upreps_bar:
            set_immutable(o)
        return Upreps, Upreps_bar

    def get_covering(self,depth):
        return self.subdivide([BTEdge(False, o) for o in self.get_BT_reps_twisted()], 1, depth - 1)

    def get_Zp_covering(self, depth):
        return self.subdivide([BTEdge(False, o) for o in self.get_BT_reps_twisted()[1:]], 1, depth - 1)

    def subdivide(self,edgelist,parity,depth):
        if depth < 0:
            return []
        if depth == 0:
            for rev,gamma in edgelist:
                set_immutable(gamma)
                return edgelist
        newEgood = []
        for rev,gamma in edgelist:
            if parity % 2 == 0:
                newEgood.extend([BTEdge(not rev, e * gamma) for e in self.get_BT_reps_twisted()[1:]])
            else:
                newEgood.extend([BTEdge(not rev, e * gamma) for e in self.get_BT_reps()[1:]])
        return self.subdivide(newEgood,1-parity,depth - 1)

    def set_wp(self, wp):
        epsinv = matrix(QQ,2,2,[0, -1, self.p, 0])**-1
        set_immutable(wp)
        assert is_in_Gamma0loc(self.embed(wp,20) * epsinv, det_condition = False)
        assert all((self.is_in_Gpn_order(wp**-1 * g * wp) for g in self.Gpn._get_O_basis()))
        assert self.is_in_Gpn_order(wp)
        self._wp = wp
        return self._wp

    def wp(self, **kwargs):
        try:
            return self._wp
        except AttributeError:
            pass
        verbose('Finding a suitable wp...')
        i = 0
        max_iterations = kwargs.get('max_iterations',-1)
        for wp in self.Gn.generate_wp_candidates(self.p,self.ideal_p,**kwargs):
            if i % 50000 == 0:
                verbose('Done %s iterations'%i)
            if i == max_iterations:
                raise RuntimeError('Trouble finding wp by enumeration')
            i += 1
            try:
                wp = self.set_wp(wp)
                verbose('wp = %s'%list(wp))
                return wp
            except AssertionError:
                pass

    def get_embedding(self,prec):
        r"""
        Returns an embedding of the quaternion algebra
        into the algebra of 2x2 matrices with coefficients in `\QQ_p`.

        INPUT:

        - prec -- Integer. The precision of the splitting.

        """
        if prec == -1:
            prec = self._prec
        if prec > self._prec: # DEBUG
            self._prec = prec
        if self.F == QQ and self.discriminant == 1:
            R =  Qp(self.p,prec)
            def iota(q):
                return q.change_ring(R)
        else:
            I,J,K = self.local_splitting(prec)
            v = self.base_ring_local_embedding(prec)
            mats = [1,I,J,K]
            def iota(q):
                R=I.parent()
                try:
                    q = q.coefficient_tuple()
                except AttributeError:
                    q = q.list()
                return sum(v(a)*b for a,b in zip(q,mats))
        return iota

    @cached_method
    def embed(self,q,prec):
        if prec is None:
            return None
        elif prec == -1:
            prec = self._prec
        if self.F == QQ and self.discriminant == 1:
            return set_immutable(q.change_ring(Qp(self.p,prec)))
        else:
            v = self.base_ring_local_embedding(prec)
            if hasattr(q,'rows'):
                return q.apply_map(v)
            try:
                return self.Gn.quaternion_to_matrix(q).apply_map(v)
            except AttributeError:
                pass
            try:
                q = q.coefficient_tuple()
            except AttributeError:
                q = q.list()
            I,J,K = self.local_splitting(prec)
            return set_immutable((v(q[0]) + v(q[1]) * I + v(q[2]) * J + v(q[3]) * K).change_ring(Qp(self.p, prec)))

    @cached_method
    def reduce_in_amalgam(self,x,return_word = False, check = True):
        a,wd = self._reduce_in_amalgam(set_immutable(x))
        if check:
            assert self.is_in_Gpn_order(a)
            tmp = a
            reps = [ self.get_BT_reps(), self.get_BT_reps_twisted() ]
            for i, j in wd:
                tmp = tmp * reps[j][i]
            assert tmp == x
        if return_word:
            return a,wd
        else:
            return a

    def coset_reps(self):
        return self.get_BT_reps()

    @cached_method
    def get_coset_ti(self, x):
        a, wd = self.reduce_in_amalgam(x, return_word = True)
        assert len(wd) <= 1
        if len(wd) == 0:
            return a, 0
        else:
            assert len(wd) == 1
            assert wd[0][1] == 0
            return a, wd[0][0]

    def _reduce_in_amalgam(self,x):
        p = self.p
        denval = lambda y, val: self.Gn._denominator_valuation(y, p) < val
        if self.Gpn._is_in_order(x):
            return x, []
        else:
            gis = [ g**-1 for g in self.get_BT_reps() ]
            gitildes = [self.Gn.B(1)] + [ g**-1 for g in self.get_BT_reps_twisted()[1:]]

            xtilde = self.do_tilde(x)
            valx = self.Gn._denominator_valuation(xtilde, p)
            if valx == 0:
                valx = 1
            i = next((i for i,g in enumerate(gitildes) if denval(xtilde * g,valx)),0)
            if i:
                x = x * gis[i]
                new_wd = [(i,0)]
            else:
                new_wd = []
            valx = self.Gn._denominator_valuation(x,p)
            if valx == 0:
                valx = 1

            if self.Gpn._is_in_order(x):
                return set_immutable(x), new_wd

            i = next((i for i,g in enumerate(gitildes) if denval(x * g,valx)),0)
            if i:
                wd1 = (i,1)
                x = set_immutable(x * gitildes[i])
                new_wd = [wd1] + new_wd
            if len(new_wd) == 0:
                print('Offending input: %s'%x)
                raise RuntimeError
            a, wd = self._reduce_in_amalgam(x)
            return set_immutable(a), wd + new_wd

    def smoothen(self,gi,ell):
        hecke_reps = gi.parent().group().get_hecke_reps(ell,use_magma = True)
        ans = gi.parent().apply_hecke_operator(gi, ell, hecke_reps = hecke_reps)
        ans -=  (ZZ(self.F(ell).norm()) + 1) * gi
        return ans

    def get_homology_kernel(self, hecke_data = None):
        verbose('Entering get_homology_kernel...')
        verb = get_verbose()
        set_verbose(0)
        if hecke_data is None:
            hecke_data = []
        wp = self.wp()
        Gn = self.Gn
        B = ArithHomology(self, ZZ**1, trivial_action = True)
        C = HomologyGroup(Gn, ZZ**1, trivial_action = True)
        group = B.group()
        Bsp = B.space()
        def phif(x):
            ans = C(0)
            for g, v in zip(group.gens(), x.values()):
                if not self.use_shapiro():
                    ans += C((Gn(g), v))
                else:
                    for a, ti in zip(v.values(), self.coset_reps()):
                        # We are considering a * (g tns t_i)
                        g0, _ = self.get_coset_ti( set_immutable(ti * g.quaternion_rep ))
                        ans += C((Gn(g0), a))
            return ans
        f = Bsp.hom([vector(C(phif(o))) for o in B.gens()])
        def phig(x):
            ans = C(0)
            for g, v in zip(group.gens(), x.values()):
                if not self.use_shapiro():
                    ans += C((Gn(wp**-1 * g.quaternion_rep * wp), v))
                else:
                    for a, ti in zip(v.values(), self.coset_reps()):
                        # We are considering a * (g tns t_i)
                        g0, _ = self.get_coset_ti( set_immutable(ti * g.quaternion_rep ))
                        ans += C((Gn(wp**-1 * g0 * wp), a))
            return ans
        g = Bsp.hom([vector(C(phig(o))) for o in B.gens()])
        maplist = [f, g]

        for ell, T in hecke_data:
            Aq = B.hecke_matrix(ell, with_torsion = True)
            tmap = Bsp.hom([sum([ZZ(a) * o for a, o in zip(col, Bsp.gens())]) for col in T.charpoly()(Aq).columns()])
            maplist.append(tmap)
        fg = direct_sum_of_maps(maplist)
        ker = fg.kernel()
        try:
            kerV = ker.V()
            good_ker = [o.lift() for o,inv in zip(ker.gens(), ker.invariants()) if inv == 0]
        except AttributeError:
            kerV = ker
            try:
                good_ker = [kerV.lift(o) for o in ker.gens()]
            except AttributeError:
                good_ker = ker.gens()
        kerVZ_amb = ZZ**(kerV.ambient_module().dimension())
        kerVZ = kerVZ_amb.submodule([kerVZ_amb(o.denominator() * o) for o in kerV.basis()])
        good_ker = kerVZ.span_of_basis([kerVZ((o.denominator() * o).change_ring(ZZ)) for o in good_ker])
        good_ker = [B(o.denominator() * o) for o in good_ker.LLL().rows()]
        set_verbose(verb)
        verbose('Done with get_homology_kernel')
        return good_ker

    def inverse_shapiro(self, x):
        Gn = self.Gn
        B = ArithHomology(self, ZZ**1, trivial_action = True)
        group = B.group()
        ans = []
        for g, v in zip(group.gens(), x.values()):
            if not self.use_shapiro():
                if v[0] == 0:
                    continue
                ans.append((group(g), ZZ(v[0])))
            else:
                for a, ti in zip(v.values(), self.coset_reps()):
                    if a[0] == 0:
                        continue
                    # We are considering a * (g tns t_i)
                    g0, _ = self.get_coset_ti( set_immutable(ti * g.quaternion_rep))
                    ans.append((Gn(g0), ZZ(a[0])))
        return ans

    def get_pseudo_orthonormal_homology(self, cocycles, hecke_data = None, outfile = None):
        if hecke_data is None:
            hecke_data = []
        ker = self.get_homology_kernel(hecke_data = tuple(hecke_data))
        assert len(ker) == 2
        f0, f1 = cocycles
        a00 = f0.pair_with_cycle(ker[0])
        a01 = f0.pair_with_cycle(ker[1])
        a10 = f1.pair_with_cycle(ker[0])
        a11 = f1.pair_with_cycle(ker[1])
        a00, a01, a10, a11 = ZZ(a00), ZZ(a01), ZZ(a10), ZZ(a11)
        determinant = a00*a11 - a01*a10
        fwrite('scaling = %s; mat = Matrix(ZZ,2,2,[%s, %s, %s, %s])'%(determinant, a00, a01, a10, a11), outfile)
        theta1 =  a11 * ker[0] - a10 * ker[1]
        theta2 = -a01 * ker[0] + a00 * ker[1]
        return theta1, theta2, determinant

def MatrixArithGroup(base = None, level = 1, implementation = 'coset_enum', **kwargs):
    if implementation not in ['coset_enum', 'geometric']:
        raise NotImplementedError
    if base is None:
        base = QQ
    if base == QQ:
        return ArithGroup_rationalmatrix(level, **kwargs)
    else:
        if base.signature() != (0,1):
            raise NotImplementedError("The base should be either QQ or an imaginary quadratic field.")
        if implementation == 'coset_enum':
            return ArithGroup_nf_matrix_new(base,level, **kwargs)
        elif implementation == 'geometric':
            return ArithGroup_nf_matrix(base, base(1), base(1), level, **kwargs)
        else:
            raise RuntimeError('Implementation should be "geometric" or "coset_enum"')

def ArithGroup(base, discriminant, abtuple = None, level = 1, magma = None, implementation=None, **kwargs):
    nscartan = kwargs.get('nscartan', None)
    if implementation is not None:
        if abtuple is not None:
            if abtuple != (1,1):
                raise ValueError('Matrix implementations only available for matrix quaternion algebra')
        else:
            if discriminant != 1:
                raise ValueError('Matrix implementations only available for matrix quaternion algebra')
    if base == QQ:
        discriminant = ZZ(discriminant)
        if discriminant == 1:
            if nscartan is not None:
                from arithgroup_nscartan import ArithGroup_nscartan
                return ArithGroup_nscartan(nscartan, level, magma=magma, **kwargs)
            else:
                return ArithGroup_rationalmatrix(level, magma=magma, **kwargs)
        else:
            if magma is None:
                raise ValueError('Should specify magma session')
            if abtuple is not None:
                return ArithGroup_rationalquaternion(abtuple, level, magma=magma, **kwargs)
            else:
                return ArithGroup_rationalquaternion(discriminant, level, magma=magma, **kwargs)
    else: # Number Field
        a,b = abtuple
        if magma is None:
            raise ValueError('Should specify magma session')
        if base.signature()[1] == 0:
            return ArithGroup_nf_fuchsian(base, a, b, level, magma=magma, **kwargs)
        else:
            if not is_page_initialized(magma):
                attach_kleinian_code(magma)
            if implementation is None:
                return ArithGroup_nf_kleinian(base, a, b, level, magma=magma, **kwargs)
            else:
                return MatrixArithGroup(base, level, implementation=implementation, magma=magma, **kwargs)
