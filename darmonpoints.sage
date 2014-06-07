##########################################################################
### Stark-Heegner points for quaternion algebras (following M.Greenberg) #
##########################################################################
from itertools import product,chain,izip,groupby,islice,tee,starmap
#from distributions import Distributions, Symk
from util import *
import os,datetime
from squatarithgp import BigArithGroup
from cohomology import CohomologyGroup,get_overconvergent_class_quaternionic
from homology import construct_homology_cycle
from integrals import integrate_H1,double_integral_zero_infty,indef_integral
from limits import find_optimal_embeddings,find_tau0_and_gtau,num_evals
from sage.misc.persist import db,db_save


try:
    page_path = ROOT + '/KleinianGroups-1.0/klngpspec'
except NameError:
    ROOT = '/home/float/GitProjects/darmonpoints' # The default, for development purposes
    page_path = ROOT + '/KleinianGroups-1.0/klngpspec'

magma.attach_spec(page_path)

sys.setrecursionlimit(10**6)

def get_overconvergent_class_matrices(p,E,prec,sign_at_infinity,use_ps_dists = False,use_sage_db = False,parallelize = False):
    # If the moments are pre-calculated, will load them. Otherwise, calculate and
    # save them to disk.
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
    print 'Computing the moments...'
    from sage.modular.pollack_stevens.space import ps_modsym_from_elliptic_curve
    phi0 = ps_modsym_from_elliptic_curve(E) #,use_ps_dists = use_ps_dists)
    #phi0 = E.PS_modular_symbol()
    if sign_at_infinity == 1:
        phi0 = phi0.plus_part()
    else:
        phi0 = phi0.minus_part()
    phi0 = 1/gcd([val.moment(0) for val in phi0.values()]) * phi0 # DEBUG
    verb_level = get_verbose()
    set_verbose(1)
    Phi = phi0.lift(p,M = prec - 1,algorithm = 'stevens',eigensymbol = True,parallel = parallelize)
    set_verbose(verb_level)
    Phi.db(fname)
    return Phi

def precompute_magma_embeddings(quat_disc,max_dK):
    level = 1
    bG = BigArithGroup(13,quat_disc,level)
    G = G.Gn
    all_embs = dict()
    ell_list = [ell for ell,_ in ZZ(quat_disc).factor()]
    for dK in range(max_dK):
        if not is_fundamental_discriminant(dK):
            continue
        if all((kronecker_symbol(dK,ell) == -1 for ell in ell_list)):
            all_embs[dK] = G.compute_quadratic_embedding(dK)
    db_save(all_embs,'quadratic_embeddings_%s_%s.sobj'%(quat_disc,level))
    print 'All done'
    return

def recognize_J(E,J,K,local_embedding = None,known_multiple = 1,twopowlist = None,outfile = None):
    p = J.parent().prime()
    prec = J.parent().precision_cap()
    QQp = Qp(p,prec)
    if local_embedding is None:
        local_embedding = QQp
    hK = K.class_number()
    Eloc = E.change_ring(local_embedding)
    # Tate parameter
    qE = tate_parameter(Eloc,QQp)

    valqE = QQ(qE.valuation())
    numqE,denqE = valqE.numerator(),valqE.denominator()

    ulog = 1/numqE * (ZZ(p)**numqE/qE**denqE).log()
    Jlog = J.log(p_branch = ulog)
    Cp = Jlog.parent()
    addpart0 = Jlog/known_multiple
    candidate = None
    if twopowlist is None:
        twopowlist = [2, 1, 1/2]
    HCF = K.hilbert_class_field(names = 'r1') if hK > 1 else K
    # Precalculate powers of qE
    qEpows = [Cp(1)]
    precp = max((prec/valqE).floor() + 4, ((prec+4)/valqE).floor() + 2)
    for i in range(precp):
        qEpows.append( qE * qEpows[-1])

    CEloc,_ = get_C_and_C2(Eloc,qEpows,Cp,precp)
    EH = E.change_ring(HCF)
    for twopow in twopowlist:
        addpart = addpart0 / twopow
        success = False

        for a,b in product(range(p),repeat = 2) if twopow * known_multiple != 1 else [(1,0)]:
            if a == 0 and b == 0:
                continue
            if twopow * known_multiple != 1:
                try:
                    J1 = Cp.teichmuller(a + Cp.gen()*b) * addpart.exp()
                except ValueError: continue
            else:
                J1 = J
            if J1 == Cp(1):
                candidate = E.change_ring(HCF)(0)
                verbose('Recognized the point, it is zero!')
                success = True
                break
            else:
                pt = getcoords(Eloc,J1,prec,qEpows = qEpows,C = CEloc)
                try:
                    x,y = pt
                except TypeError:
                    assert pt is Infinity
                    candidate = E.change_ring(HCF)(0)
                    verbose('Recognized the point, it is zero!')
                    success = True
                    break
                if x.valuation() < -(prec - 2) and y.valuation() < -(prec - 2):
                    pt = Infinity
                    candidate = E.change_ring(HCF)(0)
                    verbose('Recognized the point, it is zero!')
                    success = True
                    break
                success = False
                prec0 = prec
                while not success and prec0 > 2/3 * prec:
                    verbose('Trying to recognize point with precision %s'%prec0, level = 2)
                    candidate,success = recognize_point(x,y,E,K,prec = prec0,HCF = HCF,E_over_HCF = EH)
                    prec0 -= 1

                if success:
                    verbose('Recognized the point!')
                    fwrite('x,y = %s,%s'%(x.add_bigoh(10),y.add_bigoh(10)),outfile)
                    break
        if success:
            assert known_multiple * twopow * J1.log(p_branch = ulog) == J.log(p_branch = ulog)
            return candidate,twopow,J1
    assert not success
    return None,None,None


def darmon_point(P,E,beta,prec,working_prec = None,sign_at_infinity = 1,outfile = None,use_ps_dists = None,return_all_data = False,algorithm = None,idx_orientation = -1,magma_seed = None,use_magma = False, use_sage_db = False,idx_embedding = 0, input_data = None,quatalg_disc = None,parallelize = False,Wlist = None,twist = True,artificial_multiple = 1):
    F = E.base_ring()
    beta = F(beta)
    DB,Np = get_heegner_params(P,E,beta)
    if quatalg_disc is not None:
        assert DB == F.ideal(quatalg_disc)
        DB = quatalg_disc
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
        outfile = '/tmp/darmonpoint_%s_%s_%s_%s_%s_%s.log'%(P,Ename,dK,sgninfty,prec,datetime.datetime.now().strftime("%Y%m%d-%H%M%S"))

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
            G = BigArithGroup(P,quaternion_algebra_from_discriminant(F,DB).invariants(),Np,base = F,outfile = outfile,seed = magma_seed,use_sage_db = use_sage_db)

            # Define the cycle ( in H_1(G,Div^0 Hp) )
            try:
                cycleGn,nn,ell = construct_homology_cycle(G,beta,working_prec,hecke_smoothen = True,outfile = outfile,artificial_multiple = artificial_multiple)
            except ValueError:
                print 'ValueError occurred when constructing homology cycle. Returning the S-arithmetic group.'
                return G
            except AssertionError as e:
                print 'Assertion occurred when constructing homology cycle. Returning the S-arithmetic group.'
                print e
                return G
            smoothen_constant = -ZZ(E.reduction(ell).count_points())
            fwrite('r = %s, so a_r(E) - r - 1 = %s'%(ell,smoothen_constant),outfile)
            fwrite('exponent = %s'%nn,outfile)
            Phi = get_overconvergent_class_quaternionic(P,E,G,prec,sign_at_infinity,use_ps_dists = use_ps_dists,use_sage_db = use_sage_db,parallelize = parallelize)
            # Integration with moments
            tot_time = walltime()
            J = integrate_H1(G,cycleGn,Phi,1,method = 'moments',prec = working_prec,parallelize = parallelize,twist = twist)
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
            Phi = get_overconvergent_class_matrices(P,E,prec,sign_at_infinity,use_ps_dists = use_ps_dists,use_sage_db = use_sage_db,parallelize = parallelize)

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
    #return J,emblist
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
                if return_all_data == True:
                    return (Ptsmall, Phi, J, getcoords(E.base_extend(local_embedding),J,prec))
                else:
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
            if return_all_data == True:
                return (candidate, Phi, J, getcoords(E.base_extend(local_embedding),J,prec))
            else:
                return candidate
    else:
        fwrite('================================================',outfile)
        if return_all_data == True:
            return ([], Phi, J, getcoords(E.base_extend(local_embedding),J,prec))
        else:
            return []

