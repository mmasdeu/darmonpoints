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
from sage.structure.parent import Parent
from sage.algebras.quatalg.all import QuaternionAlgebra
from sage.matrix.all import matrix,Matrix
from sage.modules.all import vector
from sage.rings.all import RealField,ComplexField,RR,QuadraticField,PolynomialRing,NumberField,QQ,ZZ,Qp,Zmod
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
from arithgroup_element import ArithGroupElement
from sage.misc.sage_eval import sage_eval
from util import *
from sage.modules.fg_pid.fgp_module import FGP_Module
from sage.modular.arithgroup.congroup_sl2z import SL2Z
from sage.rings.finite_rings.finite_field_constructor import FiniteField
from sage.rings.infinity import Infinity
from homology_abstract import HomologyGroup
from arithgroup import ArithGroup_generic
from sage.arith.misc import XGCD
from sage.modular.modsym.p1list import lift_to_sl2z
from sage.matrix.constructor import diagonal_matrix, identity_matrix, block_diagonal_matrix
oo = Infinity

def lift(A, N):
    r"""
    Lift a matrix A from SL_m(Z/NZ) to SL_m(Z).

    Follows Shimura, Lemma 1.38, p21.

    """
    assert A.is_square()
    assert A.determinant() != 0
    m = A.nrows()
    if m == 1:
        return identity_matrix(1)

    D, U, V = A.smith_form()
    if U.determinant() == -1 :
        U = matrix(2,2,[-1,0,0,1])* U
    if V.determinant() == -1 :
        V = V *matrix(2,2,[-1,0,0,1])
    D = U*A*V
    assert U.determinant() == 1
    assert V.determinant() == 1
    a = [ D[i, i] for i in range(m) ]
    b = prod(a[1:])
    W = identity_matrix(m)
    W[0, 0] = b
    W[1, 0] = b-1
    W[0, 1] = 1
    X = identity_matrix(m)
    X[0, 1] = -a[1]
    Ap = D.parent()(D)
    Ap[0, 0] = 1
    Ap[1, 0] = 1-a[0]
    Ap[1, 1] *= a[0]
    assert (W*U*A*V*X).change_ring(Zmod(N)) == Ap.change_ring(Zmod(N))
    Cp = diagonal_matrix(a[1:])
    Cp[0, 0] *= a[0]
    C = lift(Cp, N)
    Cpp = block_diagonal_matrix(identity_matrix(1), C)
    Cpp[1, 0] = 1-a[0]
    return (~U * ~W * Cpp * ~X * ~V).change_ring(ZZ)


class ArithGroup_nscartan(ArithGroup_generic):
    Element = ArithGroupElement
    def __init__(self,q,level,info_magma = None,grouptype = None,magma = None, compute_presentation = True):
        from sage.modular.arithgroup.congroup_gamma import Gamma_constructor
        assert grouptype in ['SL2','PSL2']
        self._grouptype = grouptype
        self._compute_presentation = compute_presentation
        self.magma = magma
        self.F = QQ
        self.q = ZZ(q)
        self.discriminant = ZZ(1)
        self.level = ZZ(level/self.q)
        if self.level != 1 and compute_presentation:
            raise NotImplementedError
        self._Gamma = Gamma_constructor(self.q)
        self._Gamma_farey = self._Gamma.farey_symbol()
        self.F_units = []
        self._prec_inf = -1

        self.B = MatrixSpace(QQ,2,2)

        self._O_discriminant = ZZ.ideal(self.level * self.q)

        # Here we initialize the non-split Cartan, properly
        self.GFq = FiniteField(self.q)
        if not self.GFq(-1).is_square():
            self.eps = ZZ(-1)
        else:
            self.eps = ZZ(2)
            while self.GFq(self.eps).is_square():
                self.eps += 1
        epsinv = (self.GFq(self.eps)**-1).lift()

        N = self.level
        q = self.q
        self.Obasis = [matrix(ZZ,2,2,v) for v in [[1,0,0,1], [0,q,0,0], [0,N*epsinv,N,0], [0,0,0,q]]]

        x = QQ['x'].gen()
        K = FiniteField(self.q**2,'z',modulus = x*x - self.eps)
        x = K.primitive_element()
        x1 = x
        while x1.multiplicative_order() != self.q+1 or x1.norm() != 1:
            x1 *= x
        a, b = x1.polynomial().list() # represents a+b*sqrt(eps)
        a = a.lift()
        b = b.lift()
        self.extra_matrix = self.B(lift(matrix(ZZ,2,2,[a,b,b*self.eps,a]),self.q))
        self.extra_matrix_inverse = ~self.extra_matrix
        if compute_presentation:
            self.Ugens = []
            self._gens = []
            temp_relation_words = []
            I = SL2Z([1,0,0,1])
            E = SL2Z([-1,0,0,-1])
            minus_one = []
            for i,g in enumerate(self._Gamma_farey.generators()):
                newg = self.B([g.a(),g.b(),g.c(),g.d()])
                if newg == I:
                    continue
                self.Ugens.append(newg)
                self._gens.append(self.element_class(self,quaternion_rep = newg, word_rep = [i+1],check = False))
                if g.matrix()**2 == I.matrix():
                    temp_relation_words.append([i+1, i+1])
                    if minus_one is not None:
                        temp_relation_words.append([-i-1]+minus_one)
                    else:
                        minus_one = [i+1]
                elif g.matrix()**2 == E.matrix():
                    temp_relation_words.append([i+1,i+1,i+1,i+1])
                    if minus_one is not None:
                        temp_relation_words.append([-i-1,-i-1]+minus_one)
                    else:
                        minus_one = [i+1, i+1]
                elif g.matrix()**3 == I.matrix():
                    temp_relation_words.append([i+1, i+1, i+1])
                elif g.matrix()**3 == E.matrix():
                    temp_relation_words.append([i+1, i+1, i+1, i+1, i+1, i+1])
                    if minus_one is not None:
                        temp_relation_words.append([-i-1, -i-1, -i-1]+minus_one)
                    else:
                        minus_one = [i+1, i+1, i+1]
                else:
                    assert g.matrix()**24 != I.matrix()
            # The extra matrix is added
            i = len(self.Ugens)
            self.extra_matrix_index = i
            self.Ugens.append(self.extra_matrix)
            self._gens.append(self.element_class(self,quaternion_rep = self.Ugens[i], word_rep = [i+1],check = False))

            # The new relations are also added
            w = self._get_word_rep_initial(self.extra_matrix**(self.q+1))
            temp_relation_words.append( w + ([-i-1] * (self.q+1)))
            for j,g in enumerate(self.Ugens[:-1]):
                g1 = self.extra_matrix_inverse * g * self.extra_matrix
                w = self._get_word_rep_initial(g1)
                new_rel = w + [-i-1, -j-1, i+1]
                temp_relation_words.append(new_rel)
            self.F_unit_offset = len(self.Ugens)
            if minus_one is not None:
                self.minus_one_long = syllables_to_tietze(minus_one)
            self._relation_words = []
            for rel in temp_relation_words:
                sign = multiply_out(rel, self.Ugens, self.B(1))
                if sign == self.B(1) or 'P' in grouptype:
                    self._relation_words.append(rel)
                else:
                    assert sign == self.B(-1)
                    newrel = rel + self.minus_one
                    sign = multiply_out(newrel, self.Ugens, self.B(1))
                    assert sign == self.B(1)
                    self._relation_words.append(newrel)

        ArithGroup_generic.__init__(self)
        Parent.__init__(self)

    def _repr_(self):
        return 'Non-split Cartan with q = %s and level = %s'%(self.q,self.level)

    def _quaternion_to_list(self,x):
        return x.list()

    def generate_wp_candidates(self, p, ideal_p, **kwargs):
        eps = self.eps
        q = self.q
        for a,b in product(range(q),repeat = 2):
            if (p**2*a**2 - b**2*eps - p) % (q) == 0:
                verbose('Found a=%s, b=%s'%(a,b))
                break
        c = (self.GFq(p)**-1 * b * eps).lift()
        d = a
        a,b,c,d = lift(matrix(ZZ,2,2,[p*a,b,c,d]),q).list()
        Fp = FiniteField(p)
        if c % p == 0:
            c += a*q
            d += b*q
        assert c % p != 0
        r = (Fp(-a)*Fp(c*q)**-1).lift()
        a += q*c*r
        b += q*d*r
        ans = matrix(ZZ,2,2,[a,b,p*c,p*d])
        ans.set_immutable()
        yield ans

    # nonsplitcartan
    def embed_order(self,p,K,prec,outfile = None, return_all = False):
        r'''
        '''
        from limits import find_the_unit_of
        verbose('Computing quadratic embedding to precision %s'%prec)
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
        #####
        uk = find_the_unit_of(self.F,K)
        tu = uk.trace()
        verb_level = get_verbose()
        set_verbose(0)
        for g in self.enumerate_elements():
            if g.trace() == tu:
                gamma = self(g)
                a,b,c,d = gamma.quaternion_rep.list()
                rt_list = our_sqrt((d-a)**2 + 4*b*c,Cp,return_all=True)
                tau1, tau2 = [(Cp(a-d) + rt)/Cp(2*c) for rt in rt_list]
                assert (Cp(c)*tau1**2 + Cp(d-a)*tau1-Cp(b)) == 0
                assert (Cp(c)*tau2**2 + Cp(d-a)*tau2-Cp(b)) == 0
                r,s = uk.coordinates_in_terms_of_powers()(K.gen())
                assert r+s*uk == K.gen()
                assert uk.charpoly() == gamma.quaternion_rep.charpoly()
                mtx  = r + s*gamma.quaternion_rep
                if mtx.denominator() == 1:
                    break
        set_verbose(verb_level)
        emb = K.hom([mtx])
        mu = emb(w)
        fwrite('# \cO_K to R_0 given by w_K |-> %s'%mu,outfile)
        fwrite('# gamma_psi = %s'%gamma,outfile)
        fwrite('# tau_psi = %s'%tau1,outfile)
        fwrite('# (where g satisfies: %s)'%w.minpoly(),outfile)
        if return_all:
            return gamma, tau1, tau2
        else:
            return gamma, tau1

    def _get_word_rep_initial(self,delta): # nonsplitcartan
        level = self.level
        try:
            ans = list(self._Gamma_farey.word_problem(SL2Z(delta.list()),output = 'standard'))
        except (RuntimeError,AssertionError):
            try:
                ans = list(self._Gamma_farey.word_problem(SL2Z((-delta).list()),output = 'standard'))
            except (RuntimeError, AssertionError):
                print 'Delta = %s'%delta
                assert 0
        tmp = multiply_out(ans, self.Ugens, self.B(1))
        delta = SL2Z(delta.list())
        err = SL2Z(delta * SL2Z(tmp**-1))
        I = SL2Z([1,0,0,1])
        E = SL2Z([-1,0,0,-1])
        gens = self._Gamma_farey.generators()
        if err == I:
            return self.check_word(delta.matrix(),ans)
        else:
            assert err == E
            ans = self.minus_one_long + ans
            return self.check_word(delta.matrix(),ans)

    def _is_in_order(self, delta):
        a,b,c,d = self._quaternion_to_list(delta)
        if all([o.denominator() == 1 for o in [a,b,c,d]]):
            q = self.q
            N = self.level
            if (a-d) % q == 0 and (c - (b*self.eps)) % q == 0 and c % N == 0:
                return True
            else:
                return False
        else:
            return False

    def get_word_rep(self, delta):
        delta0 = delta
        q = self.q
        i = 0
        while not delta0 in self._Gamma:
            i += 1
            delta0 *= self.extra_matrix_inverse
        w = self._get_word_rep_initial(self.B(delta0))
        if i > 0:
            return self.check_word(delta, w + ([self.extra_matrix_index + 1] * i))
        else:
            return self.check_word(delta, w)

    def non_positive_unit(self):
        return self.element_of_norm(-1)

    def element_of_norm(self,N,use_magma = False,return_all = False, radius = None, max_elements = None, local_condition = None): # in nonsplitcartan
        try:
            if return_all:
                return [self._element_of_norm[N]]
            else:
                return self._element_of_norm[N]
        except (AttributeError,KeyError):
            pass
        if not hasattr(self,'_element_of_norm'):
            self._element_of_norm  = dict([])
        eps = self.eps
        q = self.q
        M = self.level
        llinv = (self.GFq(N)**-1).lift()
        if M != 1:
            while llinv % M != 1:
                llinv += q
        found = False
        for a,b in product(range(q*M),repeat = 2):
            if (a**2*llinv - b**2*eps*llinv - 1) % (q*M) == 0 and (b*eps) % M == 0:
                verbose('Found a=%s, b=%s'%(a,b))
                found = True
                break
        assert found
        m0 = matrix(ZZ,2,2,[a,b*llinv,b*eps,a*llinv])
        a,b,c,d = lift(m0,q*M).list()
        candidate = self.B([a,N*b,c,N*d])
        assert self._is_in_order(candidate)
        assert candidate.determinant() == N
        set_immutable(candidate)
        self._element_of_norm[N] = candidate
        if return_all:
            return [candidate]
        else:
            return candidate
