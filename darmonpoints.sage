##########################################################################
### Stark-Heegner points for quaternion algebras (following M.Greenberg) #
##########################################################################
from itertools import product,chain,izip,groupby,islice,tee,starmap
#from distributions import Distributions, Symk
from util import *
import os
from quatarithgp import BigArithGroup,load_bigarithgroup
#load 'quatarithgp.sage'
from cohomology import CohomologyGroup,get_overconvergent_class_quaternionic
from integrals import integrate_H1,double_integral_zero_infty
from limits import find_optimal_embeddings,find_tau0_and_gtau,num_evals
from sage.misc.persist import db,db_save

sys.setrecursionlimit(10**6)
def get_overconvergent_class_matrices(p,E,prec,sign_at_infinity,use_ps_dists = True,use_sage_db = True):
    # If the moments are pre-calculated, will load them. Otherwise, calculate and
    # save them to disk.
    if use_ps_dists == False:
        raise NotImplementedError
    sgninfty = 'plus' if sign_at_infinity == 1 else 'minus'
    fname = 'moments_%s_%s_%s_%s.sobj'%(p,E.cremona_label(),sgninfty,prec)
    if use_sage_db:
        try:
            Phi = db(fname)
            return Phi
        except IOError: pass
    print 'Computing the moments...'
    from pollack_stevens.space import ps_modsym_from_elliptic_curve
    #phi0 = ps_modsym_from_elliptic_curve(E,use_ps_dists = use_ps_dists)
    phi0 = E.PS_modular_symbol()
    if sign_at_infinity == 1:
        phi0 = phi0.plus_part()
    else:
        phi0 = phi0.minus_part()
    phi0 = 1/gcd([val.moment(0) for val in phi0.values()]) * phi0
    verb_level = get_verbose()
    set_verbose(1)
    Phi = phi0.lift(p,M = prec,algorithm = 'stevens',eigensymbol = True)
    set_verbose(verb_level)
    Phi.db(fname)
    return Phi

def darmon_point(p,E,dK,prec,working_prec = None,sign_at_infinity = 1,outfile = None,use_ps_dists = False,return_all_data = False,algorithm = None,magma_seed = None,use_sage_db = True):
    DB,Np = get_heegner_params(p,E.conductor(),dK)
    quaternionic = ( DB != 1 )
    QQp = Qp(p,prec)
    extra_conductor_sq = dK/fundamental_discriminant(dK)
    assert ZZ(extra_conductor_sq).is_square()
    extra_conductor = extra_conductor_sq.sqrt()
    dK = dK / extra_conductor_sq
    if dK % 4 == 0:
        dK = ZZ(dK/4)
    if working_prec is None:
        working_prec = prec + 2

    # Tate parameter
    qE = tate_parameter(E,QQp)

    # Compute the completion of F at p
    F.<r> = QuadraticField(dK)
    w = F.maximal_order().ring_generators()[0]
    r0,r1 = w.coordinates_in_terms_of_powers()(F.gen())
    Cp = Qp(p,working_prec).extension(w.minpoly(),names = 'g')
    v0 = F.hom([r0+r1*Cp.gen()])

    sgninfty = 'plus' if sign_at_infinity == 1 else 'minus'
    fname = 'moments_%s_%s_%s_%s.sobj'%(p,E.cremona_label(),sgninfty,prec)

    print "Computing the Darmon point attached to the data:"
    print 'D_B = %s = %s'%(DB,factor(DB))
    print 'Np = %s'%Np
    print 'dK = %s'%dK
    print "The calculation is being done with p = %s and prec = %s"%(p,working_prec)
    print "Should find points in the elliptic curve:"
    print E
    print "Moments will be stored in database as %s"%(fname)
    fwrite("Starting computation of the Darmon point",outfile)
    fwrite('D_B = %s  %s'%(DB,factor(DB)),outfile)
    fwrite('Np = %s'%Np,outfile)
    fwrite('dK = %s'%dK,outfile)
    fwrite('Calculation with p = %s and prec = %s+%s'%(p,prec,working_prec-prec),outfile)
    fwrite('Elliptic curve %s: %s'%(E.cremona_label(),E),outfile)
    if outfile is not None:
        print "Partial results will be saved in %s/%s"%(os.getcwd(),outfile)
    print "=================================================="


    if quaternionic:
        # Define the S-arithmetic group
        G = BigArithGroup(p,DB,Np,outfile = outfile,seed = magma_seed)

        # Define the cycle ( in H_1(G,Div^0 Hp) )
        cycleGn,nn,ell = G.construct_cycle(dK,prec,hecke_smoothen = True,outfile = outfile)
        smoothen_constant = E.ap(ell)- ell - 1
        fwrite('a_r(E) - r - 1 = %s'%smoothen_constant,outfile)
        fwrite('exponent = %s'%nn,outfile)
        Phi = get_overconvergent_class_quaternionic(p,E,G,prec,sign_at_infinity,use_ps_dists = use_ps_dists,use_sage_db = use_sage_db)
        # Integration with moments
        tot_time = walltime()
        J = integrate_H1(G,cycleGn,Phi,1,method = 'moments',prec = working_prec)
        verbose('integration tot_time = %s'%walltime(tot_time))
        G.save_to_db()
    else:
        nn = 1
        smoothen_constant = 1
        if algorithm is None:
            if Np == 1:
                algorithm = 'darmon_pollack'
            else:
                algorithm = 'guitart_masdeu'
        Phi = get_overconvergent_class_matrices(p,E,prec,sign_at_infinity,use_ps_dists = use_ps_dists,use_sage_db = use_sage_db)

        # Optimal embeddings of level one
        print "Computing optimal embeddings of level one..."
        Wlist = find_optimal_embeddings(F,use_magma = True, extra_conductor = extra_conductor)
        print "Found %s such embeddings."%len(Wlist)

        # Find the orientations
        orients = F.maximal_order().ring_generators()[0].minpoly().roots(Zmod(Np),multiplicities = False)
        print "Possible orientations: %s"%orients
        if len(Wlist) == 1 or idx_orientation == -1:
            print "Using all orientations, since h_F = 1"
            chosen_orientation = None
        else:
            print "Using orientation = %s"%orients[idx_orientation]
            chosen_orientation = orients[idx_orientation]

        J = 1
        Jlist = []
        emblist = []
        for i,W in enumerate(Wlist):
            print i, " Computing period attached to the embedding: %s"%W.list()
            tau, gtau,sign,limits = find_tau0_and_gtau(v0,Np,W,algorithm = algorithm,orientation = chosen_orientation,extra_conductor = extra_conductor)
            emblist.append((tau,gtau,sign,limits))
            print "Embedding found, now computing the period..."
            n_evals = sum((num_evals(t1,t2) for t1,t2 in limits))
            verbose('Will perform a total of %s evaluations...'%n_evals)
            newJ = prod((double_integral_zero_infty(Phi,t1,t2) for t1,t2 in limits))**sign
            Jlist.append(newJ)
            J *= newJ

    fwrite('J_psi = %s'%J,outfile)
    #Try to recognize a generator
    valqE = QQ(qE.valuation())
    numqE,denqE = valqE.numerator(),valqE.denominator()
    ulog = 1/numqE * (p**numqE/qE**denqE).log()
    Jlog = J.log(p_branch = ulog)
    Cp = Jlog.parent()

    ppow = 1
    while smoothen_constant % p == 0 :
        ppow *= p
        smoothen_constant = ZZ(smoothen_constant/p)

    addpart0 = Jlog/(smoothen_constant*nn)
    candidate = None
    twopowlist = [8, 4, 2, 1, 1/2, 1/4]
    for twopow in twopowlist:
        addpart = addpart0 / twopow
        for a,b in product(range(p),repeat = 2):
            if a == 0 and b == 0:
                continue
            # print a,b
            multpart = Cp.teichmuller(a + Cp.gen()*b)
            try:
                J1 = multpart * addpart.exp()
            except ValueError:
                continue
            if J1 == Cp(1):
                candidate = E(0)
                verbose('Recognized the point, it is zero!')
                break
            else:
                pt = getcoords(E,J1,prec)
                if pt is Infinity:
                    continue
                else:
                    x,y = pt
                success = False
                prec0 = prec
                while not success and 2*prec0 > prec:
                    verbose('Trying to recognize point with precision %s'%prec0, level = 2)
                    candidate,success = recognize_point(x,y,E.change_ring(F),prec = prec0)
                    prec0 -= 1
                if success:
                    verbose('Recognized the point!')
                    fwrite('x,y = %s,%s'%(x.add_bigoh(10),y.add_bigoh(10)),outfile)
                    break
        if success:
            try:
                verbose('candidate = %s'%candidate)
                Ptsmall = E.change_ring(F)(candidate)
                alldivs = [Ptsmall]
                m0 = 1
                for m in [3,5]:
                    while any([o.is_divisible_by(m) for o in alldivs]):
                        alldivs = [pt for o in alldivs for pt in o.division_points(m)]
                        m0 *= m
                fwrite('m0 = %s'%m0,outfile)
                fwrite('twopow = %s'%twopow,outfile)
                if twopow < 1:
                    tmp = (J1**(smoothen_constant * nn * m0))/(J**ZZ(1/twopow))
                else:
                    tmp = (J1**(smoothen_constant * nn * m0 * twopow))/J
                if tmp != 1:
                    fwrite('Constant multiples do not match...',outfile)
                fwrite('Computed point:  %s * %s * %s'%(twopow*m0,smoothen_constant * nn,Ptsmall),outfile)
                fwrite('(first factor is not understood, second factor is)',outfile)
                if ppow != 1:
                    fwrite('Took the %s-power %s out also'%(p,ppow),outfile)
                fwrite('(r satisfies %s = 0)'%(Ptsmall[0].parent().gen().minpoly()),outfile)
                fwrite('================================================',outfile)
                if return_all_data == True:
                    return Ptsmall, Phi, J, getcoords(E,J,prec)
                else:
                    return Ptsmall
            except (TypeError,ValueError):
                verbose("Could not recognize the point.")
    fwrite('================================================',outfile)
    if return_all_data == True:
        return [], Phi, J, getcoords(E,J,prec)
    else:
        return []
