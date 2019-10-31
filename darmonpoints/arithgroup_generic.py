######################
##                  ##
##    GENERIC       ##
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
from arithgroup_element import ArithGroupElement

class ArithGroup_generic(AlgebraicGroup):
    Element = ArithGroupElement
    def __init__(self):
        super(ArithGroup_generic,self).__init__()

    def base_field(self):
        return self.F

    def base_ring(self):
        return self.F

    def _an_element_(self):
        return self.gen(0)

    def get_relation_words(self):
        return self._relation_words

    @cached_method
    def get_relation_matrix(self):
        # Define the (abelian) relation matrix
        rel_words = self.get_relation_words()
        relation_matrix = matrix(ZZ,len(rel_words),len(self.gens()),0)
        for i,rel in enumerate(rel_words):
            for j in rel:
                relation_matrix[i,ZZ(j).abs() - 1] += ZZ(j).sign()
        return relation_matrix

    def one(self):
        return self.element_class(self,word_rep = [],quaternion_rep = self.B(1),check = False)

    def _element_constructor_(self,x):
        if isinstance(x,int):
            if x == 0:
                return self.zero()
            elif x == 1:
                return self.one()
            else:
                raise ValueError('Wrong input')
        if isinstance(x,list):
            return self.element_class(self, word_rep = x,check = False)
        elif isinstance(x, self.element_class):
            if x.parent() is self:
                word_rep = x.word_rep if x.has_word_rep else None
                return self.element_class(self, quaternion_rep = x.quaternion_rep, word_rep = word_rep, check = False)
            elif not x.has_word_rep:
                return self.element_class(self, quaternion_rep = x.quaternion_rep, word_rep = None, check = False)
            else:
                Gx = x.parent()
                word_rep = sum((self.get_word_rep(Gx.gen(ZZ(i).abs() - 1).quaternion_rep**ZZ(i).sign()) for i in x.word_rep),[])
                return self.element_class(self, quaternion_rep = x.quaternion_rep, word_rep = word_rep, check = False)
        elif isinstance(x.parent(),FreeModule_generic):
            return self.abelianization().ab_to_G(x)
        elif x.parent() is self.B:
            return self.element_class(self, quaternion_rep = x, check = False)
        else:
            try:
                x = x.quaternion_rep
            except AttributeError: pass
            return self.element_class(self, quaternion_rep = x,check = False)

    def generate_wp_candidates(self, p, ideal_p,**kwargs):
        epsinv = matrix(QQ,2,2,[0,-1,p,0])**-1
        if self.F == QQ:
            all_elts = self.element_of_norm(ideal_p,use_magma = True,return_all = True,radius = -1, max_elements = 1)
        else:
            all_elts = self.element_of_norm(ideal_p.gens_reduced()[0],use_magma = True,return_all = True,radius = -1, max_elements = 1)
        found = False
        all_initial = all_elts
        if len(all_initial) == 0:
            raise RuntimeError('Found no initial candidates for wp')
        verbose('Found %s initial candidates for wp'%len(all_initial))
        try:
            pgen = ideal_p.gens_reduced()[0]
        except AttributeError:
            pgen = ideal_p
        for v1,v2 in cantor_diagonal(self.enumerate_elements(),self.enumerate_elements()):
            for tmp in all_initial:
                new_candidate =  v1 * tmp * v2
                yield new_candidate

    def _coerce_map_from_(self,S):
        r"""
        The only things that coerce into this group are:
        - lists
        - elements in the quaternion algebra, of reduced norm 1
        """
        if isinstance(S,list):
            return True
        return False

    def _quaternion_to_list(self,x):
        raise NotImplementedError

    def _is_in_order(self,x):
        return self._denominator(set_immutable(x)) == 1

    def _denominator(self,x):
        return lcm([ZZ(o.denominator()) for o in self._quaternion_to_list(x)])

    def _denominator_valuation(self,x,l):
        return max((o.denominator().valuation(l) for o in self._quaternion_to_list(x)))

    def quaternion_algebra(self):
        return self.B

    def enumerate_elements(self,max_length = None):
        gens = self.gens()
        Ugens = [o.quaternion_rep for o in gens] + [o.quaternion_rep**-1 for o in gens if o.quaternion_rep != 1]
        for v in enumerate_words(range(len(Ugens))):
            if max_length is not None and len(v) > max_length:
                raise StopIteration
            else:
                yield prod([Ugens[i] for i in v],self.B(1))

    @cached_method(key = lambda self, l, use_magma, g0, progress: (self, l))
    def get_hecke_reps(self,l,use_magma = True,g0 = None,progress = False): # generic
        r'''
        TESTS:

        sage: from darmonpoints.sarithgroup import ArithGroup
        sage: magma.eval('SetSeed(2000000)') #  optional - magma
        ''
        sage: G = ArithGroup(QQ,6,None,5,magma=Magma()) # optional - magma
        sage: reps = G.get_hecke_reps(11) # optional - magma
        '''
        if l == Infinity:
            reps = [self.non_positive_unit()]
        elif l == -Infinity:
            reps = [self.wp()]
        else:
            if g0 is None:
                g0 = self.element_of_norm(l,use_magma = use_magma)
            reps = [g0]
            I = self.enumerate_elements()
            n_iters = ZZ(0)
            if self.F == QQ:
                lnorm = ZZ(l).abs()
                try:
                    num_reps = lnorm if ZZ(self._O_discriminant) % lnorm == 0 else lnorm + 1
                except TypeError:
                    num_reps = lnorm if ZZ(self._O_discriminant.gen()) % ZZ(lnorm) == 0 else lnorm + 1
            else:
                lnorm = self.F.ideal(l).norm()
                num_reps = lnorm if self.F.ideal(l).divides(self._O_discriminant) else lnorm + 1

            while len(reps) < num_reps:
                n_iters += 1
                new_candidate = next(I) * g0
                new_inv = new_candidate**-1
                if not any([self._is_in_order(new_inv * old) for old in reps]):
                    reps.append(new_candidate)
                if progress and n_iters % 100 == 0:
                    update_progress(float(len(reps))/float(num_reps),'Getting Hecke representatives (%s iterations)'%(n_iters))
            if progress:
                update_progress(float(1.0),'Getting Hecke representatives (%s iterations)'%(n_iters))
        return tuple([set_immutable(o) for o in reps])

    @cached_method
    def get_hecke_ti(self,gk1,gamma,l = None,use_magma = False, reps = None):
        r"""

        INPUT:

        - gk1 - a quaternion element of norm l
        - gamma - an element of G
        - If l is None, it is assumed to be p.

        OUTPUT:

        - t_{gk1}(gamma)

        """
        elt = gk1**-1 * gamma.quaternion_rep
        if reps is None:
            reps = self.get_Up_reps() if l is None else self.get_hecke_reps(l,use_magma = use_magma)
        for gk2 in reps:
            ti = elt * gk2
            is_in_order = self._is_in_order(ti)
            if self._is_in_order(ti):
                if l is None and self.embed(set_immutable(ti),20)[1,0].valuation() > 0: # Up
                    return self(ti)
                else:
                    return self(ti)
        verbose("ti not found. gk1 = %s, gamma = %s, l = %s"%(gk1,gamma,l))
        raise RuntimeError("ti not found. gk1 = %s, gamma = %s, l = %s"%(gk1,gamma,l))

    def gen(self,i):
        return self._gens[i]

    def gens(self):
        return self._gens

    def check_word(self,delta,wd):
        Ugens = [o.quaternion_rep for o in self.gens()]
        tmp = multiply_out(wd, Ugens, self.B(1))
        assert tmp == delta,"tmp = %s, delta = %s, wd = %s"%(tmp,delta,wd)
        return wd

    def _calculate_relation(self,wt,separated = False):
        relmat = self.get_relation_matrix()
        relwords = self.get_relation_words()
        num_rels = len(relwords)
        if num_rels == 0:
            return []
        f= (ZZ**num_rels).hom(relmat.rows())
        linear_combination = f.lift(wt)
        ans = []
        for i,lam in enumerate(linear_combination):
            relation = relwords[i]
            if lam == 0:
                continue
            else:
                if separated:
                    if lam < 0:
                        ans.append((ZZ(-lam),relation))
                    else:
                        ans.append((ZZ(lam),[-j for j in reversed(relation)]))
                else:
                    if lam < 0:
                        ans += ZZ((-lam))*relation
                    else: #lam > 0
                        ans += ZZ(lam)*[-j for j in reversed(relation)]
        return ans

    def get_weight_vector(self,x):
        gens = self.gens()
        weight_vector = vector(ZZ,[0 for g in gens])
        for i in x.word_rep:
            if i > 0:
                weight_vector[i-1] += 1
            else:
                weight_vector[-i-1] -= 1
        return weight_vector

    def calculate_weight_zero_word(self, xlist, separated = False):
        Gab = self.abelianization()
        abxlist = [n * Gab(x) for x,n in xlist]
        sum_abxlist = vector(sum(abxlist))
        if not sum_abxlist == 0:
            raise ValueError('Must yield trivial element in the abelianization (%s)'%(sum_abxlist))
        oldwordlist = [copy(x.word_rep) for x,n in xlist]
        return oldwordlist, self._calculate_relation(sum(n * self.get_weight_vector(x) for x,n in xlist), separated = separated)

    def decompose_into_commutators(self,x):
        oldwordlist, rel = self.calculate_weight_zero_word([x])
        assert len(oldwordlist) == 1
        oldword = oldwordlist[0] + rel
        # At this point oldword has weight vector 0
        # We use the identity:
        # C W0 g^a W1 = C [W0,g^a] g^a W0 W1
        commutator_list = []
        for i in xrange(len(self.gens())):
            while True:
                # Find the first occurence of generator i
                try:
                    idx = [x[0] for x in oldword[1:]].index(i) + 1
                except ValueError:
                    break
                w0 = self._element_constructor_(oldword[:idx])
                gatmp = [oldword[idx]]
                ga = self._element_constructor_(gatmp)
                oldword = gatmp + oldword[:idx] + oldword[idx+1:]
                w0q = w0.quaternion_rep
                gaq = ga.quaternion_rep
                commute = w0q * gaq * w0q**-1 * gaq**-1
                if commute != 1:
                    commutator_list.append((w0,ga))
        assert len(oldword) == 0
        return commutator_list

    @cached_method
    def abelianization(self):
        from homology_abstract import Abelianization
        return Abelianization(self)

    def find_matrix_from_cusp(self, cusp):
        r'''
        Returns a matrix gamma and a cusp representative modulo Gamma0(N) (c2:d2),
        represented as a matrix (a,b;c,d), such that gamma * cusp = (c2:d2).

        HACK: inputting a,c manually as we don't have cusp package
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
                    ax+cy = 1.
                """
                if a.parent() != c.parent():
                    raise ValueError('a,c not in the same field.')
                else:
                    OK = a.parent()
                if a.gcd(c) != 1:
                    raise ValueError('a,c not coprime.')

                d = next(x for x in OK.ideal(c).residues() if a * x - 1 in OK.ideal(c))
                b = (1 - a * x) / c
                # d,b = xgcd_F(a,-c)

            g = Matrix(2,2,[d,-b,-c,a]) # the inverse
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

        ## Loop over all points of P^1(O_F/N)
        while len(remaining_points) > 0:
            ## Pick a new cusp representative
            c = remaining_points.pop()
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