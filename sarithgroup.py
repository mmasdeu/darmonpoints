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
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,NumberField,lcm,QQ,ZZ,Qp,Zmod
from sage.functions.trig import arctan
from sage.interfaces.magma import magma
from sage.misc.misc_c import prod
from collections import defaultdict
from itertools import product,chain,izip,groupby,islice,tee,starmap
from arithgroup import ArithGroup_nf_quaternion,ArithGroup_rationalquaternion,ArithGroup_rationalmatrix
from sigma0 import Sigma0,Sigma0ActionAdjuster
from util import *
from homology import Divisors, Homology
from sage.structure.sage_object import save,load
from copy import copy
from sage.misc.persist import db
from sage.modules.free_module import FreeModule_generic

class BTEdge(SageObject):
    r'''
    A BTEdge is represented by an element `gamma`, and then a flag called `reverse`.
    The flag reverse indicates whether we refer to the opposite edge of the one
    represented by `gamma`.
    '''
    def __init__(self,reverse,gamma):
        self.reverse = reverse
        self.gamma = gamma

    def _repr_(self):
        return "(%s)^%s"%(self.gamma,'+' if self.reverse == False else '-')

    def __iter__(self):
        return iter([self.reverse,self.gamma])

def BigArithGroup(p,quat_data,level,base = None, seed = None,use_sage_db = True,outfile = None):
        # if seed is None:
        #     seed = 1000
        try:
            discriminant = ZZ(quat_data)
            if base is not None:
                assert base == QQ
            else:
                base = QQ
            fname = 'arithgroup%s_%s_%s_%s.sobj'%(seed,p,discriminant,level) # Fix this name
        except TypeError:
            discriminant = None
            a,b = quat_data
            if base is None:
                base = a.parent()
            fname = 'arithgroup%s_%s_%s_%s.sobj'%(seed,p,discriminant,level) # Fix this name
        if base != QQ:
            use_sage_db = False # This is not implemented yet

        if use_sage_db:
            try:
                newobj = db(fname)
            except IOError:
                verbose('Group not found in database. Computing from scratch.')
                newobj = BigArithGroup_class(base,p,discriminant,level,seed,outfile = outfile)
                newobj.save_to_db()
        else:
            if discriminant is None:
                discriminant = QuaternionAlgebra(base,a,b).discriminant()
                newobj = BigArithGroup_class(base,p,discriminant,abtuple = (a,b),level = level,seed = seed,outfile = outfile)
            else:
                newobj = BigArithGroup_class(base,p,discriminant,level = level,seed = seed,outfile = outfile)
        return newobj


class BigArithGroup_class(AlgebraicGroup):
    r'''
    This class holds information about the group `\Gamma`: a finite
    presentation for it, a solution to the word problem,...

    Initializes the group attached to a `\ZZ[1/p]`-order of the rational quaternion algebra of
    discriminant `discriminant` and  level `n`.

    TESTS:

        sage: G = BigArithGroup(7,15,1)
        sage: a = G([(1,2),(0,3),(2,-1)])
        sage: b = G([(1,3)])
        sage: c = G([(2,1)])
        sage: print a*b
        Element in Arithmetic Group attached to data p = 7, disc = 15, level = 1
        Word representation: [(1, 2), (0, 3), (2, -1), (1, 3)]
        sage: a.quaternion_rep
        618 + 787/4*i - 239*j - 787/4*k
        sage: b.quaternion_rep
        -1
        sage: print a*b
        Element in Arithmetic Group attached to data p = 7, disc = 15, level = 1
        Quaternion representation: -618 - 787/4*i + 239*j + 787/4*k
        Word representation: [(1, 2), (0, 3), (2, -1), (1, 3)]
    '''
    def __init__(self,base,p,discriminant,abtuple = None,level = 1,seed = None,outfile = None):
        self.seed = seed
        if seed is not None:
            verbose('Setting Magma seed to %s'%seed)
            magma.eval('SetSeed(%s)'%seed)
        self.F = base
        if self.F.degree() > 1:
            Fideal = self.F.maximal_order().ideal
        self.ideal_p = Fideal(p) if self.F.degree() > 1 else ZZ(p)
        self.norm_p = ZZ(p.norm()) if self.F.degree() > 1 else ZZ(p)
        self.p = self.norm_p.prime_divisors()[0]
        if not self.ideal_p.is_prime():
            raise ValueError, 'p ( = %s) must be prime'%self.p
        self.discriminant = Fideal(discriminant) if self.F.degree() > 1 else ZZ(discriminant)
        self.level = Fideal(level) if self.F.degree() > 1 else ZZ(level)
        verbose('Initializing arithmetic group G(n)...')
        self.Gn = ArithGroup(self.F,self.discriminant,abtuple,self.level)
        self.Gn.get_embedding = self.get_embedding
        self.Gn.embed = self.embed
        verbose('Initializing arithmetic group G(pn)...')
        self.Gpn = ArithGroup(self.F,self.discriminant,abtuple,self.ideal_p*self.level,info_magma = self.Gn)
        fwrite('B = Q<i,j,k>, with i^2 = %s and j^2 = %s'%(self.Gn.B.gens()[0]**2,self.Gn.B.gens()[1]**2),outfile)
        try:
            basis_data_1 = list(self.Gn.Obasis)
            basis_data_p = list(self.Gpn.Obasis)
        except AttributeError:
            basis_data_1 = self.Gn.basis_invmat.inverse().columns()
            basis_data_p = self.Gpn.basis_invmat.inverse().columns()
        fwrite('R with basis %s'%basis_data_1,outfile)
        fwrite('R(p) with basis %s'%basis_data_p,outfile)
        self.Gpn.get_embedding = self.get_embedding
        self.Gpn.embed = self.embed
        # self._prec = -1
        self._II,self._JJ,self._KK = self._compute_padic_splitting(60)

        self.wp = self._compute_wp()
        self.get_Up_reps()
        verbose('Done initializing arithmetic groups')
        self.Gpn.get_Up_reps = self.get_Up_reps

        try:
            self.Gn._ArithGroup_generic__delete_unused_attributes()
            self.Gpn._ArithGroup_generic__delete_unused_attributes()
        except AttributeError: pass

        verbose('Done initialization of BigArithmeticGroup')

    def clear_cache(self):
        self.Gn.clear_cache()
        self.Gpn.clear_cache()

    def _repr_(self):
       return 'S-Arithmetic Rational Group attached to data p = %s,  disc = %s, level = %s'%(self.p,self.discriminant,self.level)

    def prime(self):
        return self.p

    def base_ring_local_embedding(self,prec):
        if prec > self._prec:
            self._compute_padic_splitting(prec)
        return self._F_to_local

    def _compute_padic_splitting(self,prec):
        verbose('Entering compute_padic_splitting')
        prime = self.p
        if self.seed is not None:
            magma.eval('SetSeed(%s)'%self.seed)
        R = Qp(prime,prec) #Zmod(prime**prec) #
        B_magma = self.Gn._B_magma
        verbose('Calling magma pMatrixRing')
        if self.F == QQ:
            M,f,_ = magma.pMatrixRing(self.Gn._Omax_magma.name(),prime*self.Gn._Omax_magma.BaseRing(),nvals = 3)
            self._F_to_local = QQ.hom([R(1)])
        else:
            M,f,_ = magma.pMatrixRing(self.Gn._Omax_magma.name(),sage_F_ideal_to_magma(self.Gn._F_magma,self.ideal_p),nvals = 3)
            self._F_to_local = self.F.hom([R(f.Image(B_magma(B_magma.BaseRing().gen(1))).Vector()[1]._sage_())])
        self.Gn._F_to_local = self._F_to_local
        self.Gpn._F_to_local = self._F_to_local
        verbose('Initializing II,JJ,KK')
        v = f.Image(B_magma.gen(1)).Vector()
        self._II = matrix(R,2,2,[v[i+1]._sage_() for i in range(4)])
        v = f.Image(B_magma.gen(2)).Vector()
        self._JJ = matrix(R,2,2,[v[i+1]._sage_() for i in range(4)])
        v = f.Image(B_magma.gen(3)).Vector()
        self._KK = matrix(R,2,2,[v[i+1]._sage_() for i in range(4)])
        # Test splitting
        mats = [matrix(R,2,2,[1,0,0,1]),self._II,self._JJ,self._KK]
        for g in self.Gpn.Obasis:
            tup = g.coefficient_tuple()
            mat = sum([self._F_to_local(a) * b for a,b in zip(tup,mats)])
            assert is_in_Gamma0loc(mat,det_condition = False)
        self._prec = prec
        return self._II, self._JJ, self._KK

    def _local_splitting(self,prec):
        r"""
        Finds an embedding of the definite quaternion algebra
        into the algebra of 2x2 matrices with coefficients in `\QQ_p`.

        INPUT:

        - prec -- Integer. The precision of the splitting.

        OUTPUT:

        - Matrices I, J, K giving the splitting.

        EXAMPLES::

            sage: X = BigArithGroup(13,2*3,1)
            sage: phi = X._local_splitting(10)
            sage: B.<i,j,k> = QuaternionAlgebra(3)
            sage: phi(i)**2 == QQ(i**2)*phi(B(1))
            True

        """
        if prec <= self._prec:
            return self._II,self._JJ,self._KK
        self._II,self._JJ,self._KK = self._compute_padic_splitting(prec)

        return self._II, self._JJ, self._KK

    def save_to_db(self):
        fname = 'arithgroup%s_%s_%s_%s.sobj'%(self.seed,self.p,self.discriminant,self.level)
        self.db(fname)

    def small_group(self):
        return self.Gpn

    def large_group(self):
        return self.Gn

    @cached_method
    def get_BT_reps(self):
        reps = [self.Gn.B(1)] + [None for i in range(self.p)]
        emb = self.get_embedding(5)
        matrices = [(i+1,matrix(QQ,2,2,[i,1,-1,0])) for i in range(self.p)]
        for n_iters,elt in enumerate(self.Gn.enumerate_elements()):
            new_inv = elt**(-1)
            if all([not self.Gpn._is_in_order(o * new_inv) for o in reps if o is not None]):
                for idx,o1 in enumerate(matrices):
                    i,mat = o1
                    embelt = emb(elt)
                    if (embelt[0,0]-1).valuation() > 0:
                        tmp = embelt * mat
                        if is_in_Gamma0loc(tmp):
                            reps[i] = set_immutable(elt)
                            del matrices[idx]
                            verbose('%s, len = %s/%s'%(n_iters,self.p+1-len(matrices),self.p+1))
                            if len(matrices) == 0:
                                return reps
                            break

    def do_tilde(self,g):
        # lam = -self.p
        lam = -self.wp.reduced_norm()
        # lam = -self.F(self.ideal_p.gen(0)) if self.F.degree() > 1 else -self.p
        return 1/lam * self.wp * g * self.wp # FIXME

    @cached_method
    def get_BT_reps_twisted(self):
        return [self.Gn.B(1)] + [self.do_tilde(g) for g in self.get_BT_reps()[1:]]

    @cached_method
    def get_Up_reps(self):
        # lam = -self.p
        lam = -self.wp.reduced_norm()
        # lam = -self.F(self.ideal_p.gen(0)) if self.F.degree() > 1 else -self.p
        tmp = [ lam * o**-1 * self.wp**-1 for o in self.get_BT_reps()[1:]] #FIXME
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

    #@lazy_attribute
    def _compute_wp(self):
        verbose('Finding a suitable wp...')
        if self.discriminant == 1:
            return matrix(QQ,2,2,[0,-1,self.p,0])
        else:
            epsinv = matrix(QQ,2,2,[0,-1,self.p,0])**-1
            pfacts = self.F.maximal_order().ideal(self.p).factor() if self.F.degree() > 1 else ZZ(self.p).factor()

            all_elts = self.Gpn.element_of_norm(self.ideal_p,use_magma = False,return_all = True, radius = 5,max_elements = 1) #FIXME
            found = False
            all_initial = all_elts
            if len(all_initial) == 0:
                raise RuntimeError
            verbose('Found %s initial candidates for wp'%len(all_initial))
            i = 0
            try:
                pgen = self.ideal_p.gen(0)
            except AttributeError:
                pgen = self.ideal_p
            for v1,v2 in cantor_diagonal(self.Gn.enumerate_elements(),self.Gn.enumerate_elements()):
                if i % 1000 == 0:
                    verbose('Done %s iterations'%i)
                i += 1
                for tmp in all_initial:
                    new_candidate =  v2 * tmp * v1
                    if is_in_Gamma0loc(epsinv * self.embed(new_candidate,20), det_condition = False) and all((self.Gpn._is_in_order(new_candidate**-1 * g * new_candidate) for g in self.Gpn.Obasis)) and self.Gpn._is_in_order(new_candidate): # and self.Gpn._is_in_order(new_candidate**2/pgen): #FIXME: is last condition needed?
                        return new_candidate
            raise RuntimeError

    def get_embedding(self,prec):
        r"""
        Returns an embedding of the quaternion algebra
        into the algebra of 2x2 matrices with coefficients in `\QQ_p`.

        INPUT:

        - prec -- Integer. The precision of the splitting.

        """
        if self.discriminant == 1:
            R =  Qp(self.p,prec)
            def iota(q):
                return q.change_ring(R)
        else:
            I,J,K = self._local_splitting(prec)
            mats = [1,I,J,K]
            def iota(q):
                R=I.parent()
                try:
                    q = q.coefficient_tuple()
                except AttributeError: pass
                return sum(self._F_to_local(a)*b for a,b in zip(q,mats))
        return iota

    @cached_method
    def embed(self,q,prec):
        if prec is None:
            return None
        if self.discriminant == 1:
            return q.change_ring(Qp(self.p,prec))
        else:
            try:
                q = q.coefficient_tuple()
            except AttributeError: pass
            I,J,K = self._local_splitting(prec)
            f = self._F_to_local
            return f(q[0]) + f(q[1]) * I + f(q[2]) * J + f(q[3]) * K

    def reduce_in_amalgam(self,x,return_word = False):
        rednrm = x.reduced_norm() if self.discriminant != 1 else x.determinant()
        if rednrm != 1:
            raise ValueError,'x (= %s) must have reduced norm 1'%x
        a,wd = self._reduce_in_amalgam(set_immutable(x))
        if return_word:
            return a,wd
        else:
            return a

    def _reduce_in_amalgam(self,x):
        x0 = x
        p = self.p
        denval = self.Gn._denominator_valuation
        if self.Gpn._denominator(x) == 1:
            return x,[]
        else:
            gis = [ g**-1 for g in self.get_BT_reps()]
            gitildes = [self.Gn.B(1)] + [ g**-1 for g in self.get_BT_reps_twisted()[1:]]

            xtilde = self.do_tilde(x)
            valx = denval(xtilde,p)
            if valx == 0:
                valx = 1
            found = False

            i = next((i for i,g in enumerate(gitildes) if denval(xtilde * g,p) < valx),0)
            wd0 = (i,0)
            x = x * gis[i]

            valx = denval(x,p)
            if valx == 0:
                valx = 1

            if self.Gpn._denominator(x) == 1:
                return x, [wd0]

            i = next((i for i,g in enumerate(gitildes) if denval(x * g,p) < valx),0)
            assert i > 0
            wd1 = (i,1)
            x = set_immutable(x * gitildes[i])
            a,wd = self._reduce_in_amalgam(x)
            return a, wd + [wd1,wd0]


def ArithGroup(base,discriminant,abtuple = None,level = 1,info_magma = None):
    if base == QQ:
        discriminant = ZZ(discriminant)
        if discriminant == 1:
            return ArithGroup_rationalmatrix(level,info_magma)
        else:
            if abtuple is not None:
                return ArithGroup_rationalquaternion(abtuple,level,info_magma)
            else:
                return ArithGroup_rationalquaternion(discriminant,level,info_magma)
    else:
        a,b = abtuple
        return ArithGroup_nf_quaternion(base,a,b,level,info_magma)
