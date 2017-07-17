######################################
#####     Curve finding           ####
######################################
from sage.rings.padics.precision_error import PrecisionError
from util import discover_equation,fwrite,quaternion_algebra_invariants_from_ramification, direct_sum_of_maps, config_section_map, Bunch
from sarithgroup import BigArithGroup
from homology import lattice_homology_cycle
from cohomology_arithmetic import ArithCoh, get_overconvergent_class_quaternionic
from integrals import integrate_H1,double_integral_zero_infty
from sage.all import QQ, ZZ, Qp, QuaternionAlgebra, factor, Infinity
import sys, os, datetime, ConfigParser

def find_curve(P, DB, NE, prec, sign_ap = None, magma = None, return_all = False, initial_data = None, ramification_at_infinity = None, **kwargs):
    r'''
    EXAMPLES:

    First example::

    sage: from darmonpoints.findcurve import find_curve
    sage: find_curve(5,6,30,20) # long time # optional - magma
    # B = F<i,j,k>, with i^2 = -1 and j^2 = 3
    ...
    '(1, 0, 1, -289, 1862)'

    A second example, now over a real quadratic::

    sage: from darmonpoints.findcurve import find_curve
    sage: F.<r> = QuadraticField(5)
    sage: P = F.ideal(3/2*r + 1/2)
    sage: D = F.ideal(3)
    sage: find_curve(P,D,P*D,30,ramification_at_infinity = F.real_places()[:1]) # long time # optional - magma
    ...

    Now over a cubic of mixed signature::

    sage: from darmonpoints.findcurve import find_curve
    sage: F.<r> = NumberField(x^3 -3)
    sage: P = F.ideal(r-2)
    sage: D = F.ideal(r-1)
    sage: find_curve(P,D,P*D,30) # long time # optional - magma
    ...

    '''
    config = ConfigParser.ConfigParser()
    config.read('config.ini')
    param_dict = config_section_map(config, 'General')
    param_dict.update(config_section_map(config, 'FindCurve'))
    param_dict.update(kwargs)
    param = Bunch(**param_dict)

    # Get general parameters
    outfile = param.get('outfile')
    use_ps_dists = param.get('use_ps_dists',False)
    use_shapiro = param.get('use_shapiro',True)
    use_sage_db = param.get('use_sage_db',False)
    magma_seed = param.get('magma_seed',1515316)
    parallelize = param.get('parallelize',False)
    Up_method = param.get('up_method','naive')
    use_magma = param.get('use_magma',True)
    progress_bar = param.get('progress_bar',True)
    sign_at_infinity = param.get('sign_at_infinity',ZZ(1))

    # Get find_curve specific parameters
    grouptype = param.get('grouptype')
    hecke_bound = param.get('hecke_bound',3)
    timeout = param.get('timeout',0)
    check_conductor = param.get('check_conductor',True)

    if initial_data is None:
        page_path = os.path.dirname(__file__) + '/KleinianGroups-1.0/klngpspec'
        if magma is None:
            from sage.interfaces.magma import Magma
            quit_when_done = True
            magma = Magma()
        else:
            quit_when_done = False
        if magma_seed is not None:
            magma.eval('SetSeed(%s)'%magma_seed)
        magma.attach_spec(page_path)
        magma.eval('Page_initialized := true')
    else:
        quit_when_done = False

    sys.setrecursionlimit(10**6)

    # global qE, Linv, G, Coh, phiE, xgen, xi1, xi2, Phi

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

    Ncartan = kwargs.get('Ncartan',None)
    Np = NE / (P * DB)
    if Ncartan is not None:
        Np = Np / Ncartan**2
    if use_ps_dists is None:
        use_ps_dists = False # More efficient our own implementation

    if not p.is_prime():
        raise ValueError,'P (= %s) should be a prime, of inertia degree 1'%P

    working_prec = max([2 * prec + 10, 100])

    sgninfty = 'plus' if sign_at_infinity == 1 else 'minus'
    fname = 'moments_%s_%s_%s_%s_%s_%s.sobj'%(Fdisc,p,DB,NE,sgninfty,prec)

    if outfile == 'log':
        outfile = '%s_%s_%s_%s_%s.log'%(P,NE,sgninfty,prec,datetime.datetime.now().strftime("%Y%m%d-%H%M%S"))
        outfile = outfile.replace('/','div')
        outfile = '/tmp/findcurve_' + outfile

    if F != QQ and ramification_at_infinity is None:
        if F.signature()[0] > 1:
            if F.signature()[1] == 1:
                ramification_at_infinity = F.real_places(prec = Infinity) # Totally 'definite'
            else:
                raise ValueError,'Please specify the ramification at infinity'
        elif F.signature()[0] == 1:
            if len(F.ideal(DB).factor()) % 2 == 0:
                ramification_at_infinity = [] # Split at infinity
            else:
                ramification_at_infinity = F.real_places(prec = Infinity) # Ramified at infinity
        else:
            ramification_at_infinity = None

    if outfile is not None:
        print("Partial results will be saved in %s"%outfile)

    if initial_data is not None:
        G,phiE = initial_data
    else:
        # Define the S-arithmetic group
        try:
            if F == QQ:
                abtuple = QuaternionAlgebra(DB).invariants()
            else:
                abtuple = quaternion_algebra_invariants_from_ramification(F,DB,ramification_at_infinity)
            G = BigArithGroup(P, abtuple, Np, use_sage_db = use_sage_db, grouptype = grouptype, magma = magma, seed = magma_seed, timeout = timeout, use_shapiro = use_shapiro, nscartan = Ncartan)
        except RuntimeError as e:
            if quit_when_done:
                magma.quit()
            mystr = str(e)
            if len(mystr) > 30:
                mystr = mystr[:14] + ' ... ' + mystr[-14:]
            if return_all:
                return ['Error when computing G: ' + mystr]
            else:
                return 'Error when computing G: ' + mystr

        # Define phiE, the cohomology class associated to the system of eigenvalues.
        Coh = ArithCoh(G)
        try:
            phiE = Coh.get_rational_cocycle(sign = sign_at_infinity,bound = hecke_bound,return_all = return_all,use_magma = True)
        except Exception as e:
            if quit_when_done:
                magma.quit()
            if return_all:
                return ['Error when finding cohomology class: ' + str(e)]
            else:
                return 'Error when finding cohomology class: ' + str(e)
        if use_sage_db:
            G.save_to_db()
        fwrite('Cohomology class found', outfile)
    try:
        ker = [G.inverse_shapiro(o) for o in G.get_homology_kernel()]
    except Exception as e:
        if quit_when_done:
            magma.quit()
        if return_all:
            return ['Problem calculating homology kernel: ' + str(e)]
        else:
            return 'Problem calculating homology kernel: ' + str(e)

    if not return_all:
        phiE = [phiE]
    ret_vals = []
    for phi in phiE:
        try:
            Phi = get_overconvergent_class_quaternionic(P,phi,G,prec,sign_at_infinity,sign_ap,use_ps_dists,method = Up_method, progress_bar = progress_bar)
        except ValueError as e:
            ret_vals.append('Problem when getting overconvergent class: ' + str(e))
            continue
        fwrite('Done overconvergent lift', outfile)
        # Find an element x of Gpn for not in the kernel of phi,
        # and such that both x and wp^-1 * x * wp are trivial in the abelianization of Gn.
        try:
            found = False
            for o in ker:
                phi_o = sum( [phi.evaluate(t**a) for t, a in o], 0 )
                if use_shapiro:
                    phi_o = phi_o.evaluate_at_identity()
                if phi_o != 0:
                    found = True
                    break
            if not found:
                raise RuntimeError('Cocycle evaluates always to zero')
        except Exception as e:
            ret_vals.append('Problem when choosing element in kernel: ' + str(e))
            continue
        xgenlist = o
        found = False
        while not found:
            try:
                xi1, xi2 = lattice_homology_cycle(G,xgenlist,working_prec,outfile = outfile)
                found = True
            except PrecisionError:
                working_prec  = 2 * working_prec
                verbose('Setting working_prec to %s'%working_prec)
            except Exception as e:
                ret_vals.append('Problem when computing homology cycle: ' + str(e))
                verbose('Exception occurred: ' + str(e))
                break
        if not found:
            continue
        try:
            qE1 = integrate_H1(G,xi1,Phi,1,method = 'moments',prec = working_prec, twist = False,progress_bar = progress_bar)
            qE2 = integrate_H1(G,xi2,Phi,1,method = 'moments',prec = working_prec, twist = True,progress_bar = progress_bar)
        except Exception as e:
            ret_vals.append('Problem with integration: %s'%str(e))
            continue

        qE = qE1/qE2
        qE = qE.add_bigoh(prec + qE.valuation())
        Linv = qE.log(p_branch = 0)/qE.valuation()

        fwrite('Integral done. Now trying to recognize the curve', outfile)
        fwrite('F.<r> = NumberField(%s)'%(F.gen(0).minpoly()),outfile)
        fwrite('N_E = %s = %s'%(NE,factor(NE)),outfile)
        fwrite('D_B = %s = %s'%(DB,factor(DB)),outfile)
        fwrite('Np = %s = %s'%(Np,factor(Np)),outfile)
        if Ncartan is not None:
            fwrite('Ncartan = %s'%(Ncartan),outfile)
        fwrite('Calculation with p = %s and prec = %s+%s'%(P,prec,working_prec-prec),outfile)
        fwrite('qE = %s'%qE,outfile)
        fwrite('Linv = %s'%Linv,outfile)
        curve = discover_equation(qE,G._F_to_local,NE,prec,check_conductor = check_conductor)
        if curve is None:
            if quit_when_done:
                magma.quit()
            ret_vals.append('None')
        else:
            try:
                curve = curve.global_minimal_model()
            except AttributeError,NotImplementedError:
                pass
            fwrite('EllipticCurve(F, %s )'%(list(curve.a_invariants())), outfile)
            fwrite('=' * 60, outfile)
            ret_vals.append(str(curve.a_invariants()))
    if quit_when_done:
        magma.quit()
    if return_all:
        return ret_vals
    else:
        return ret_vals[0]
