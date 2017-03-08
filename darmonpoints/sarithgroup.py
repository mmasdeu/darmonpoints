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
from collections import defaultdict
from itertools import product,chain,izip,groupby,islice,tee,starmap
from arithgroup import ArithGroup_nf_quaternion,ArithGroup_rationalquaternion,ArithGroup_rationalmatrix
from arithgroup_nscartan import ArithGroup_nscartan
from util import *
from sage.structure.sage_object import save,load
from copy import copy
from sage.misc.persist import db
from sage.modules.free_module import FreeModule_generic
import os,datetime
from homology_abstract import ArithHomology, HomologyGroup

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

def BigArithGroup(p,quat_data,level,base = None, grouptype = None,seed = None,use_sage_db = False,outfile = None, magma = None, timeout = 0, logfile = None, use_shapiro = True, character = None, nscartan = None):
    if magma is None:
        from sage.interfaces.magma import Magma
        magma = Magma(logfile = logfile)
        page_path = os.path.dirname(__file__) + '/KleinianGroups-1.0/klngpspec'
        if seed is not None:
            magma.eval('SetSeed(%s)'%seed)
        magma.attach_spec(page_path)
    magma.eval('Page_initialized := true')
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
            grouptype = 'PGL2'

    if use_sage_db:
        try:
            newobj = db(fname)
        except IOError:
            verbose('Group not found in database. Computing from scratch.')
            newobj = BigArithGroup_class(base,p,discriminant,level,seed,outfile = outfile,grouptype = grouptype,magma = magma,timeout = timeout, use_shapiro = use_shapiro, character = character, nscartan = nscartan)
            newobj.save_to_db()
    else:
        if a is not None:
            newobj = BigArithGroup_class(base,p,discriminant,abtuple = (a,b),level = level,seed = seed,outfile = outfile,grouptype = grouptype,magma = magma,timeout = timeout, use_shapiro = use_shapiro, character = character, nscartan = nscartan)
        else:
            newobj = BigArithGroup_class(base,p,discriminant,level = level,seed = seed,outfile = outfile,grouptype = grouptype,magma = magma,timeout = timeout, use_shapiro = use_shapiro, character = character, nscartan = nscartan)
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
        sage: print a * b # random #  optional - magma
        -236836769/2 + 120098645/2*i - 80061609/2*j - 80063439/2*k
        sage: b.quaternion_rep # random #  optional - magma
        846 - 429*i + 286*j + 286*k
    '''
    def __init__(self,base,p,discriminant,abtuple = None,level = 1,grouptype = None,seed = None,outfile = None,magma = None,timeout = 0, use_shapiro = True, character = None, nscartan = None):
        self.seed = seed
        self.magma = magma
        self._use_shapiro = use_shapiro
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
        lev = self.ideal_p*self.level
        if character is not None:
            lev = [lev, character]
        self.Gpn = ArithGroup(self.F,self.discriminant,abtuple,lev,grouptype = grouptype,magma = magma, compute_presentation = not self._use_shapiro, timeout = timeout,nscartan=nscartan)
        self.Gpn.get_embedding = self.get_embedding
        self.Gpn.embed = self.embed
        verbose('Initializing arithmetic group G(n)...')
        lev = self.level
        if character is not None:
            lev = [lev, character]
        self.Gn = ArithGroup(self.F,self.discriminant,abtuple,lev,info_magma = self.Gpn,grouptype = grouptype,magma = magma, compute_presentation = True, timeout = timeout,nscartan=nscartan)
        t = walltime(t)
        verbose('Time for calculation T = %s'%t)
        verbose('T = %s x difficulty'%RealField(25)(t/difficulty))

        self.Gn.get_embedding = self.get_embedding
        self.Gn.embed = self.embed
        if hasattr(self.Gn.B,'is_division_algebra'):
            fwrite('# B = F<i,j,k>, with i^2 = %s and j^2 = %s'%(self.Gn.B.gens()[0]**2,self.Gn.B.gens()[1]**2),outfile)
        else:
            fwrite('# B = M_2(F)',outfile)
        try:
            basis_data_1 = list(self.Gn.Obasis)
            if not self.use_shapiro():
                basis_data_p = list(self.Gpn.Obasis)
        except AttributeError:
            try:
                basis_data_1 = self.Gn.basis_invmat.inverse().columns()
                if not self.use_shapiro():
                    basis_data_p = self.Gpn.basis_invmat.inverse().columns()
            except AttributeError:
                basis_data_1 = '?'
                basis_data_p = '?'
        self._prec = -1
        self.get_embedding(200)
        fwrite('# R with basis %s'%basis_data_1,outfile)
        self.Gn.get_Up_reps = self.get_Up_reps
        if not self.use_shapiro():
            fwrite('# R(p) with basis %s'%basis_data_p,outfile)
            self.Gpn.get_Up_reps = self.get_Up_reps
        self.Gn.wp = self.wp
        self.Gpn.wp = self.wp
        verbose('Done initializing arithmetic groups')
        verbose('Done initialization of BigArithmeticGroup')

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

    def base_ring_local_embedding(self,prec):
        if self.F == QQ:
            return lambda x:x
        else:
            self.local_splitting(prec)
            return self._F_to_local

    def _compute_padic_splitting(self,prec):
        verbose('Entering compute_padic_splitting')
        prime = self.p
        if self.seed is not None:
            self.magma.eval('SetSeed(%s)'%self.seed)
        R = Qp(prime,prec+10) #Zmod(prime**prec) #
        B_magma = self.Gn._B_magma
        a,b = self.Gn.B.invariants()
        if (a,b) == (1,1): # DEBUG
            self._II = matrix(R,2,2,[1,0,0,-1])
            self._JJ = matrix(R,2,2,[0,1,1,0])
            goodroot = self.F.gen().minpoly().change_ring(R).roots()[0][0]
            self._F_to_local = self.F.hom([goodroot])
        else:
            verbose('Calling magma pMatrixRing')
            if self.F == QQ:
                _,f = self.magma.pMatrixRing(self.Gn._O_magma,prime*self.Gn._O_magma.BaseRing(),Precision = 20,nvals = 2)
                self._F_to_local = QQ.hom([R(1)])
            else:
                _,f = self.magma.pMatrixRing(self.Gn._O_magma,sage_F_ideal_to_magma(self.Gn._F_magma,self.ideal_p),Precision = 20,nvals = 2)
                try:
                    self._goodroot = R(f.Image(B_magma(B_magma.BaseRing().gen(1))).Vector()[1]._sage_())
                except SyntaxError:
                    raise SyntaxError("Magma has trouble finding local splitting")
                self._F_to_local = None
                for o,_ in self.F.gen().minpoly().change_ring(R).roots():
                    if (o - self._goodroot).valuation() > 5:
                        self._F_to_local = self.F.hom([o])
                        break
                assert self._F_to_local is not None
            verbose('Initializing II,JJ,KK')
            v = f.Image(B_magma.gen(1)).Vector()
            self._II = matrix(R,2,2,[v[i+1]._sage_() for i in xrange(4)])
            v = f.Image(B_magma.gen(2)).Vector()
            self._JJ = matrix(R,2,2,[v[i+1]._sage_() for i in xrange(4)])
            v = f.Image(B_magma.gen(3)).Vector()
            self._KK = matrix(R,2,2,[v[i+1]._sage_() for i in xrange(4)])
            self._II , self._JJ = lift_padic_splitting(self._F_to_local(a),self._F_to_local(b),self._II,self._JJ,prime,prec)
        self.Gn._F_to_local = self._F_to_local
        if not self.use_shapiro():
            self.Gpn._F_to_local = self._F_to_local

        self._KK = self._II * self._JJ
        self._prec = prec
        return self._II, self._JJ, self._KK

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
        if prec <= self._prec:
            return self._II,self._JJ,self._KK
        return self._compute_padic_splitting(prec)

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
        return self.Gpn.Obasis

    def Gpn_denominator(self, x):
        return self.Gpn._denominator(x)

    @cached_method
    def get_BT_reps(self):
        reps = [self.Gn.B(1)] + [None for i in xrange(self.p)]
        emb = self.get_embedding(20)
        matrices = [(i+1,matrix(QQ,2,2,[i,1,-1,0])) for i in xrange(self.p)]
        for n_iters,elt in enumerate(self.Gn.enumerate_elements()):
            new_inv = elt**(-1)
            embelt = emb(elt)
            if (embelt[0,0]-1).valuation() > 0 and all([not self.is_in_Gpn_order(o * new_inv) for o in reps if o is not None]):
                if hasattr(self.Gpn,'nebentypus'):
                    tmp = self.do_tilde(embelt)**-1
                    tmp = tmp[0,0] / (self.p**tmp[0,0].valuation()) # DEBUG
                    tmp = ZZ(tmp.lift()) % self.Gpn.level
                    if tmp not in self.Gpn.nebentypus:
                        continue
                for idx,o1 in enumerate(matrices):
                    i,mat = o1
                    if is_in_Gamma0loc(embelt * mat, det_condition = False):
                        reps[i] = set_immutable(elt)
                        del matrices[idx]
                        # update_progress(float((self.p+1-len(matrices)))/float(self.p+1),'Getting BT representatives (%s iterations)'%(n_iters))
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
        wp = self.wp()
        if self.F == QQ and self.discriminant == 1:
            lam = -wp.determinant()
        else:
            lam = -wp.reduced_norm()
        tmp = [ lam * o**-1 * wp**-1 for o in self.get_BT_reps()[1:]]
        for o in tmp:
            set_immutable(o)
        return tmp

    def get_covering(self,depth):
        return self.subdivide([BTEdge(False, o) for o in self.get_BT_reps_twisted()], 1, depth - 1)

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
        epsinv = matrix(QQ,2,2,[0,-1,self.p,0])**-1
        set_immutable(wp)
        assert is_in_Gamma0loc(self.embed(wp,20) * epsinv, det_condition = False)
        assert all((self.is_in_Gpn_order(wp**-1 * g * wp) for g in self.Gpn_Obasis()))
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
        if self.F == QQ and self.discriminant == 1:
            R =  Qp(self.p,prec)
            self._F_to_local = QQ.hom([R(1)])
            def iota(q):
                return q.change_ring(R)
        else:
            I,J,K = self.local_splitting(prec)
            mats = [1,I,J,K]
            def iota(q):
                R=I.parent()
                try:
                    q = q.coefficient_tuple()
                except AttributeError:
                    q = q.list()
                return sum(self._F_to_local(a)*b for a,b in zip(q,mats))
        return iota

    @cached_method
    def embed(self,q,prec):
        if prec is None:
            return None
        if self.F == QQ and self.discriminant == 1:
            return set_immutable(q.change_ring(Qp(self.p,prec)))
        else:
            try:
                q = q.coefficient_tuple()
            except AttributeError: pass
            I,J,K = self.local_splitting(prec)
            f = self._F_to_local
            return set_immutable((f(q[0]) + f(q[1]) * I + f(q[2]) * J + f(q[3]) * K).change_ring(Qp(self.p, prec)))

    @cached_method
    def reduce_in_amalgam(self,x,return_word = False, check = False):
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
                print 'Offending input: %s'%x
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
        Gn = self.large_group()
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
        Gn = self.large_group()
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

def ArithGroup(base,discriminant,abtuple = None,level = 1,info_magma = None, grouptype = None,magma = None, compute_presentation = True, timeout = 0, nscartan = None):
    if base == QQ:
        if timeout != 0:
            raise NotImplementedError("Timeout not implemented for rational base yet")
        discriminant = ZZ(discriminant)
        if discriminant == 1:
            if nscartan is not None:
                return ArithGroup_nscartan(nscartan,level,info_magma,grouptype = grouptype, magma = magma, compute_presentation = compute_presentation)
            else:
                return ArithGroup_rationalmatrix(level,info_magma,grouptype = grouptype, magma = magma, compute_presentation = compute_presentation)
        else:
            if magma is None:
                raise ValueError('Should specify magma session')

            if abtuple is not None:
                return ArithGroup_rationalquaternion(abtuple,level,info_magma,grouptype = grouptype,magma = magma, compute_presentation = compute_presentation)
            else:
                return ArithGroup_rationalquaternion(discriminant,level,info_magma,grouptype = grouptype,magma = magma, compute_presentation = compute_presentation)
    else:
        a,b = abtuple
        if magma is None:
            raise ValueError('Should specify magma session')
        return ArithGroup_nf_quaternion(base,a,b,level,info_magma,grouptype = grouptype,magma = magma,timeout = timeout, compute_presentation = compute_presentation)
