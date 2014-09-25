from itertools import product,chain,izip,groupby,islice,tee,starmap
from sage.modules.fg_pid.fgp_module import FGP_Module,FGP_Module_class
from sage.matrix.constructor import matrix,Matrix,block_diagonal_matrix,block_matrix
from util import tate_parameter,update_progress,get_C_and_C2,getcoords,recognize_point,fwrite
import os,datetime
from sage.misc.persist import db
load('fmpz_mat.spyx')

##########################################################################
### Stark-Heegner points for quaternion algebras                         #
##########################################################################

def darmon_point(P,E,beta,prec,working_prec = None,sign_at_infinity = 1,outfile = None,use_ps_dists = None,algorithm = None,idx_orientation = -1,magma_seed = None,use_magma = False, use_sage_db = False,idx_embedding = 0, input_data = None,parallelize = False,Wlist = None,twist = True, progress_bar = True, magma = None, Up_method = None):
    global G, Coh, phiE, Phi, dK, J, J1, cycleGn, nn, Jlist
    from util import get_heegner_params,fwrite,quaternion_algebra_from_discriminant, recognize_J
    from sarithgroup import BigArithGroup
    from homology import construct_homology_cycle
    from cohomology import get_overconvergent_class_matrices, get_overconvergent_class_quaternionic, CohomologyGroup

    from integrals import double_integral_zero_infty,indef_integral,integrate_H1
    from limits import find_optimal_embeddings,find_tau0_and_gtau,num_evals

    try:
        page_path = ROOT + '/KleinianGroups-1.0/klngpspec'
    except NameError:
        ROOT = os.getcwd()
        page_path = ROOT + '/KleinianGroups-1.0/klngpspec'
    if magma is None:
        from sage.interfaces.magma import Magma
        magma = Magma()
        quit_when_done = True
    else:
        quit_when_done = False

    magma.attach_spec(page_path)
    sys.setrecursionlimit(10**6)

    F = E.base_ring()
    beta = F(beta)
    DB,Np = get_heegner_params(P,E,beta)
    quaternionic = ( DB != 1 )
    if use_ps_dists is None:
        use_ps_dists = False if quaternionic else True
    try:
        p = ZZ(P)
    except TypeError:
        p = ZZ(P.norm())
    if not p.is_prime():
        raise ValueError,'P (= %s) should be a prime, of inertia degree 1'%P

    QQp = Qp(p,prec)
    if F == QQ:
        dK = ZZ(beta)
        extra_conductor_sq = dK/fundamental_discriminant(dK)
        assert ZZ(extra_conductor_sq).is_square()
        extra_conductor = extra_conductor_sq.sqrt()
        dK = dK / extra_conductor_sq
        assert dK == fundamental_discriminant(dK)
        if dK % 4 == 0:
            dK = ZZ(dK/4)
        beta = dK
    else:
        dK = beta

    if working_prec is None:
        working_prec = 2 * prec + 10

    # Compute the completion of K at p
    x = QQ['x'].gen()
    K = F.extension(x**2 - dK,names = 'alpha') #QuadraticField(dK,names = 'r')
    if F == QQ:
        dK = K.discriminant()
    else:
        dK = K.relative_discriminant()

    hK = K.class_number()

    sgninfty = 'plus' if sign_at_infinity == 1 else 'minus'
    if hasattr(E,'cremona_label'):
        Ename = E.cremona_label()
    else:
        Ename = E.ainvs()

    fname = 'moments_%s_%s_%s_%s.sobj'%(P,Ename,sgninfty,prec)

    print "Computing the Darmon point attached to the data:"
    print 'D_B = %s = %s'%(DB,factor(DB))
    print 'Np = %s'%Np
    print 'dK = %s'%dK
    print "The calculation is being done with p = %s and prec = %s"%(p,working_prec)
    print "Should find points in the elliptic curve:"
    print E
    if use_sage_db:
        print "Moments will be stored in database as %s"%(fname)

    if outfile is None:
        outfile = '%s_%s_%s_%s_%s_%s.log'%(P,Ename,dK,sgninfty,prec,datetime.datetime.now().strftime("%Y%m%d-%H%M%S"))
        outfile = outfile.replace('/','div')
        outfile = '/tmp/darmonpoint_' + outfile

    fwrite("Starting computation of the Darmon point",outfile)
    fwrite('D_B = %s  %s'%(DB,factor(DB)),outfile)
    fwrite('Np = %s'%Np,outfile)
    fwrite('dK = %s (class number = %s)'%(dK,hK),outfile)
    fwrite('Calculation with p = %s and prec = %s+%s'%(P,prec,working_prec-prec),outfile)
    fwrite('Elliptic curve %s: %s'%(Ename,E),outfile)
    if outfile is not None:
        print "Partial results will be saved in %s"%outfile
    print "=================================================="

    if input_data is None:
        if quaternionic:
            # Define the S-arithmetic group
            G = BigArithGroup(P,quaternion_algebra_from_discriminant(F,DB).invariants(),Np,base = F,outfile = outfile,seed = magma_seed,use_sage_db = use_sage_db,magma = magma)

            # Define the cycle ( in H_1(G,Div^0 Hp) )
            try:
                cycleGn,nn,ell = construct_homology_cycle(G,beta,working_prec,hecke_smoothen = True,outfile = outfile)
            except ValueError:
                print 'ValueError occurred when constructing homology cycle. Returning the S-arithmetic group.'
                if quit_when_done:
                    magma.quit()
                return G
            except AssertionError as e:
                print 'Assertion occurred when constructing homology cycle. Returning the S-arithmetic group.'
                print e
                if quit_when_done:
                    magma.quit()
                return G
            smoothen_constant = -ZZ(E.reduction(ell).count_points())
            fwrite('r = %s, so a_r(E) - r - 1 = %s'%(ell,smoothen_constant),outfile)
            fwrite('exponent = %s'%nn,outfile)
            phiE = CohomologyGroup(G.small_group()).get_cocycle_from_elliptic_curve(E,sign = sign_at_infinity)
            if hasattr(E,'cremona_label'):
                Ename = E.cremona_label()
            elif hasattr(E,'ainvs'):
                Ename = E.ainvs()
            else:
                Ename = 'unknown'
            Phi = get_overconvergent_class_quaternionic(P,phiE,G,prec,sign_at_infinity,use_ps_dists = use_ps_dists,use_sage_db = use_sage_db,parallelize = parallelize,method = Up_method, progress_bar = progress_bar,Ename = Ename)
            # Integration with moments
            tot_time = walltime()
            J = integrate_H1(G,cycleGn,Phi,1,method = 'moments',prec = working_prec,parallelize = parallelize,twist = twist,progress_bar = progress_bar)
            verbose('integration tot_time = %s'%walltime(tot_time))
            if use_sage_db:
                G.save_to_db()
        else:
            nn = 1
            smoothen_constant = 1
            if algorithm is None:
                if Np == 1:
                    algorithm = 'darmon_pollack'
                else:
                    algorithm = 'guitart_masdeu'

            w = K.maximal_order().ring_generators()[0]
            r0,r1 = w.coordinates_in_terms_of_powers()(K.gen())
            Cp = Qp(p,working_prec).extension(w.minpoly(),names = 'g')
            v0 = K.hom([r0+r1*Cp.gen()])

            # Optimal embeddings of level one
            if Wlist is None:
                print "Computing optimal embeddings of level one..."
                Wlist = find_optimal_embeddings(K,use_magma = use_magma, extra_conductor = extra_conductor)
                print "Found %s such embeddings."%len(Wlist)
            if idx_embedding is not None:
                if idx_embedding >= len(Wlist):
                    print 'There are not enough embeddings. Taking the index modulo %s'%len(Wlist)
                    idx_embedding = idx_embedding % len(Wlist)
                print 'Taking only embedding number %s'%(idx_embedding)
                Wlist = [Wlist[idx_embedding]]

            # Find the orientations
            orients = K.maximal_order().ring_generators()[0].minpoly().roots(Zmod(Np),multiplicities = False)
            print "Possible orientations: %s"%orients
            if len(Wlist) == 1 or idx_orientation == -1:
                print "Using all orientations, since hK = 1"
                chosen_orientation = None
            else:
                print "Using orientation = %s"%orients[idx_orientation]
                chosen_orientation = orients[idx_orientation]

            emblist = []
            for i,W in enumerate(Wlist):
                tau, gtau,sign,limits = find_tau0_and_gtau(v0,Np,W,algorithm = algorithm,orientation = chosen_orientation,extra_conductor = extra_conductor)
                print 'n_evals = ', sum((num_evals(t1,t2) for t1,t2 in limits))
                emblist.append((tau,gtau,sign,limits))

            # Get the cohomology class from E
            Phi = get_overconvergent_class_matrices(P,E,prec,sign_at_infinity,use_ps_dists = use_ps_dists,use_sage_db = use_sage_db,parallelize = parallelize,progress_bar = progress_bar)

            J = 1
            Jlist = []
            for i,emb in enumerate(emblist):
                print i, " Computing period attached to the embedding: %s"%Wlist[i].list()
                tau, gtau,sign,limits = emb
                #print 'tau = %s'%tau
                #print 'gtau = %s'%gtau.list()
                n_evals = sum((num_evals(t1,t2) for t1,t2 in limits))
                print "Computing one period...(total of %s evaluations)"%n_evals
                newJ = prod((double_integral_zero_infty(Phi,t1,t2) for t1,t2 in limits))**ZZ(sign)
                #newJ = indef_integral(Phi,tau,gtau,limits = limits)**ZZ(sign)
                Jlist.append(newJ)
                J *= newJ
    else: # input_data is not None
        Phi,J = input_data[1:3]
    print 'Integral done. Now trying to recognize the point'
    fwrite('J_psi = %s'%J,outfile)
    #Try to recognize a generator
    if quaternionic:
        local_embedding = G.base_ring_local_embedding(working_prec)
        twopowlist = [4, 3, 2, 1, 1/2, 3/2, 1/3, 2/3, 1/4, 3/4, 5/2, 4/3]
    else:
        local_embedding = Qp(p,working_prec)
        twopowlist = [2, 1, 1/2]


    known_multiple = (smoothen_constant*nn)
    while known_multiple % p == 0:
        known_multiple = ZZ(known_multiple / p)

    candidate,twopow,J1 = recognize_J(E,J,K,local_embedding = local_embedding,known_multiple = known_multiple,twopowlist = twopowlist,outfile = outfile)

    if candidate is not None:
        HCF = K.hilbert_class_field(names = 'r1') if hK > 1 else K
        if hK == 1:
            try:
                verbose('candidate = %s'%candidate)
                Ptsmall = E.change_ring(HCF)(candidate)
                fwrite('twopow = %s'%twopow,outfile)
                fwrite('Computed point:  %s * %s * %s'%(twopow,known_multiple,Ptsmall),outfile)
                fwrite('(first factor is not understood, second factor is)',outfile)
                # if ppow != 1:
                #     fwrite('Took the %s-power %s out also'%(p,ppow),outfile)
                fwrite('(r satisfies %s = 0)'%(Ptsmall[0].parent().gen().minpoly()),outfile)
                fwrite('================================================',outfile)
                print 'Point found: %s'%Ptsmall
                if quit_when_done:
                    magma.quit()
                return Ptsmall
            except (TypeError,ValueError):
                verbose("Could not recognize the point.")
        else:
            verbose('candidate = %s'%candidate)
            fwrite('twopow = %s'%twopow,outfile)
            fwrite('Computed point:  %s * %s * (x,y)'%(twopow,known_multiple),outfile)
            fwrite('(first factor is not understood, second factor is)',outfile)
            try:
                pols = [HCF(c).relative_minpoly() for c in candidate[:2]]
            except AttributeError:
                pols = [HCF(c).minpoly() for c in candidate[:2]]
            fwrite('Where x satisfies %s'%pols[0],outfile)
            fwrite('and y satisfies %s'%pols[1],outfile)
            fwrite('================================================',outfile)
            print 'Point found: %s'%candidate
            if quit_when_done:
                magma.quit()
            return candidate
    else:
        fwrite('================================================',outfile)
        if quit_when_done:
            magma.quit()
        return []


######################################
#####     Curve finding           ####
######################################


def find_curve(P,DB,NE,prec,working_prec = None,sign_at_infinity = 1,outfile = None,use_ps_dists = None,use_sage_db = False,magma_seed = None, parallelize = False,ramification_at_infinity = None,kill_torsion = True,grouptype = None, progress_bar = True,magma = None, hecke_bound = 3,Up_method = None,return_all = False,initial_data = None):
    from itertools import product,chain,izip,groupby,islice,tee,starmap
    from sage.rings.padics.precision_error import PrecisionError
    from util import discover_equation,get_heegner_params,fwrite,quaternion_algebra_from_discriminant, discover_equation_from_L_invariant,direct_sum_of_maps
    import os,datetime

    from sarithgroup import BigArithGroup
    from homology import construct_homology_cycle,lattice_homology_cycle
    from cohomology import CohomologyGroup, get_overconvergent_class_quaternionic

    from integrals import integrate_H1,double_integral_zero_infty,indef_integral
    from limits import find_optimal_embeddings,find_tau0_and_gtau,num_evals
    try:
        page_path = ROOT + '/KleinianGroups-1.0/klngpspec'
    except NameError:
        ROOT = os.getcwd()
        page_path = ROOT + '/KleinianGroups-1.0/klngpspec'

    if magma is None:
        from sage.interfaces.magma import Magma
        quit_when_done = True
        magma = Magma()
    else:
        quit_when_done = False
    magma.attach_spec(page_path)

    sys.setrecursionlimit(10**6)

    global qE, Linv, G, Coh, phiE, xgen, wxgen, xi1, xi2, curve, ker

    try:
        F = P.ring()
        Fdisc = F.discriminant()
        if not (P*DB).divides(NE):
            raise ValueError,'Conductor (NE) should be divisible by P*DB'
        p = ZZ(P.norm()).abs()

    except AttributeError:
        F = QQ
        P = ZZ(P)
        p = ZZ(P)
        Fdisc = ZZ(1)
        if NE % (P*DB) != 0:
            raise ValueError,'Conductor (NE) should be divisible by P*DB'

    Np = NE / (P*DB)
    if use_ps_dists is None:
        use_ps_dists = False # More efficient our on implementation

    if not p.is_prime():
        raise ValueError,'P (= %s) should be a prime, of inertia degree 1'%P

    QQp = Qp(p,prec)

    if working_prec is None:
        working_prec = max([2 * prec + 10,100])

    sgninfty = 'plus' if sign_at_infinity == 1 else 'minus'
    fname = 'moments_%s_%s_%s_%s_%s_%s.sobj'%(Fdisc,p,DB,NE,sgninfty,prec)

    if outfile is None:
        outfile = '%s_%s_%s_%s_%s.log'%(P,NE,sgninfty,prec,datetime.datetime.now().strftime("%Y%m%d-%H%M%S"))
        outfile = outfile.replace('/','div')
        outfile = '/tmp/findcurve_' + outfile

    if F != QQ and ramification_at_infinity is None:
        if F.signature()[0] > 1:
            if F.signature()[1] == 1:
                ramification_at_infinity = [-1 for o in range(F.signature()[0])]
            else:
                raise ValueError,'Please specify the ramification at infinity'
        elif F.signature()[0] == 1:
            if len(F.ideal(DB).factor()) % 2 == 0:
                ramification_at_infinity = [1] # Split
            else:
                ramification_at_infinity = [-1] # Ramified
        else:
            ramification_at_infinity = []

    fwrite("Starting computation of the Curve",outfile)
    fwrite('N_E = %s  %s'%(NE,factor(NE)),outfile)
    fwrite('D_B = %s  %s'%(DB,factor(DB)),outfile)
    fwrite('Np = %s'%Np,outfile)
    fwrite('Calculation with p = %s and prec = %s+%s'%(P,prec,working_prec-prec),outfile)
    if outfile is not None:
        print "Partial results will be saved in %s"%outfile
    print "=================================================="

    if initial_data is not None:
        G,phiE = initial_data
    else:
        # Define the S-arithmetic group
        try:
            G = BigArithGroup(P,quaternion_algebra_from_discriminant(F,DB,ramification_at_infinity).invariants(),Np,use_sage_db = use_sage_db,grouptype = grouptype,magma = magma)
        except Exception as e:
            if quit_when_done:
                magma.quit()
            return 'Error when computing G: ' + e.message

        # Define phiE, the cohomology class associated to the system of eigenvalues.
        try:
            Coh = CohomologyGroup(G.Gpn)
            phiE = Coh.get_rational_cocycle(sign = sign_at_infinity,bound = hecke_bound,return_all = return_all)
        except Exception as e:
            if quit_when_done:
                magma.quit()
            return 'Error when finding cohomology class: ' + e.message
        if use_sage_db:
            G.save_to_db()
        print 'Cohomology class found'
    try:
        wp = G.wp()
        B = G.Gpn.abelianization()
        C = G.Gn.abelianization()
        Bab = B.abelian_group()
        Cab = C.abelian_group()
        verbose('Finding f...')
        fdata = [B.ab_to_G(o).quaternion_rep for o in B.gens_small()]
        # verbose('fdata = %s'%fdata)
        f = B.hom_from_image_of_gens_small([C.G_to_ab(G.Gn(o)) for o in fdata])
        verbose('Finding g...')
        gdata = [wp**-1 * o * wp for o in fdata]
        # verbose('gdata = %s'%gdata)
        g = B.hom_from_image_of_gens_small([C.G_to_ab(G.Gn(o)) for o in gdata])
        fg = direct_sum_of_maps([f,g])
        V = Bab.gen(0).lift().parent()
        good_ker = V.span_of_basis([o.lift() for o in fg.kernel().gens()]).LLL().rows()
        ker = [B.ab_to_G(Bab(o)).quaternion_rep for o in good_ker]
    except Exception as e:
        if quit_when_done:
            magma.quit()
        return 'Problem calculating homology kernel: ' + e.message

    if not return_all:
        phiE = [phiE]
    ret_vals = []
    for phi in phiE:
        try:
            Phi = get_overconvergent_class_quaternionic(P,phi,G,prec,sign_at_infinity,use_ps_dists,method = Up_method, progress_bar = progress_bar)
        except Exception as e:
            ret_vals.append('Problem when getting overconvergent class: ' + e.message)
            continue
        print 'Done overconvergent lift'
        # Find an element x of Gpn for not in the kernel of phi,
        # and such that both x and wp^-1 * x * wp are trivial in the abelianization of Gn.
        try:
            found = False
            for o in ker:
                if phi.evaluate(o) != 0:
                    found = True
                    break
            if not found:
                raise RuntimeError('Cocycle evaluates always to zero')
        except Exception as e:
            ret_vals.append('Problem when choosing element in kernel: ' + e.message)
            continue

        xgen, wxgen = G.Gn(o),G.Gn(wp**-1 * o * wp)
        found = False
        while not found:
            try:
                xi1, xi2 = lattice_homology_cycle(G,xgen,wxgen,working_prec,outfile = outfile)
                found = True
            except PrecisionError:
                working_prec  = 2 * working_prec
                verbose('Setting working_prec to %s'%working_prec)
            except Exception as e:
                ret_vals.append('Problem when computing homology cycle' + e.message)
                break

        try:
            qE1 = integrate_H1(G,xi1,Phi,1,method = 'moments',prec = working_prec, twist = False,progress_bar = progress_bar)
            qE2 = integrate_H1(G,xi2,Phi,1,method = 'moments',prec = working_prec, twist = True,progress_bar = progress_bar)
        except Exception as e:
            ret_vals.append('Problem with integration' + e.message)

        qE = qE1/qE2
        qE = qE.add_bigoh(prec + qE.valuation())
        Linv = qE.log(p_branch = 0)/qE.valuation()

        print 'Integral done. Now trying to recognize the curve'
        fwrite('qE = %s'%qE,outfile)
        fwrite('Linv = %s'%Linv,outfile)
        curve = discover_equation(qE,G._F_to_local,NE,prec)
        if curve is None:
            fwrite('Curve not found with the sought conductor. Will try to find some curve at least',outfile)
            print 'Curve not found with the sought conductor. Will try to find some curve at least'
            curve = discover_equation(qE,G._F_to_local,NE,prec,check_conductor = False)
            if curve is None:
                fwrite('Still no luck. Sorry!',outfile)
                print 'Still no luck. Sorry!'
                if quit_when_done:
                    magma.quit()
                ret_vals.append(None)
                continue
            else:
                curve = curve.global_minimal_model()
                fwrite('Found a curve, at least...',outfile)
                print 'Found a curve, at least...'
        else:
            curve = curve.global_minimal_model()
        fwrite('Curve with a-invariants %s'%(list(curve.a_invariants())),outfile)
        fwrite('================================================',outfile)
        ret_vals.append((curve,qE,Linv,Phi))
    if quit_when_done:
        magma.quit()
    if return_all:
        return ret_vals
    else:
        return ret_vals[0]
