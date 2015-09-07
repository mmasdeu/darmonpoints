##########################################################################
### Stark-Heegner points for quaternion algebras                         #
##########################################################################

def darmon_point(P, E, beta, prec, ramification_at_infinity = None, input_data = None, magma = None, working_prec = None, **kwargs):
    r'''

    EXAMPLES:

    First we load the file::

    sage: %runfile darmonpoints.sage

    A first example (Stark--Heegner point)::

    sage: darmon_point(7,EllipticCurve('35a1'),41,20)

    A quaternionic (Greenberg) point::

    sage: darmon_point(13,EllipticCurve('78a1'),5,20)

    A Darmon point over a cubic (1,1) field::

    sage: F.<r> = NumberField(x^3 - x^2 - x + 2)
    sage: E = EllipticCurve([-r -1, -r, -r - 1,-r - 1, 0])
    sage: N = E.conductor()
    sage: P = F.ideal(r^2 - 2*r - 1)
    sage: beta = -3*r^2 + 9*r - 6
    sage: darmon_point(P,E,beta,20)

    '''
    global G, Coh, phiE, Phi, dK, J, J1, cycleGn, nn, Jlist
    from util import get_heegner_params,fwrite,quaternion_algebra_invariants_from_ramification, recognize_J,config_section_map, Bunch
    from sage.rings.padics.precision_error import PrecisionError
    from sarithgroup import BigArithGroup
    from homology import construct_homology_cycle
    from cohomology_arithmetic import get_overconvergent_class_matrices, get_overconvergent_class_quaternionic, ArithCoh
    from integrals import double_integral_zero_infty,integrate_H1
    from limits import find_optimal_embeddings,find_tau0_and_gtau,num_evals
    import os, datetime, ConfigParser

    config = ConfigParser.ConfigParser()
    config.read('config.ini')
    param_dict = config_section_map(config, 'General')
    param_dict.update(config_section_map(config, 'DarmonPoint'))
    param_dict.update(kwargs)
    param = Bunch(**param_dict)

    # Get general parameters
    outfile = param.outfile
    use_ps_dists = param.use_ps_dists
    use_shapiro = param.use_shapiro
    use_sage_db = param.use_sage_db
    magma_seed = param.magma_seed
    parallelize = param.parallelize
    Up_method = param.up_method
    use_magma = param.use_magma
    progress_bar = param.progress_bar
    sign_at_infinity = param.sign_at_infinity

    # Get darmon_point specific parameters
    idx_orientation = param.idx_orientation
    idx_embedding = param.idx_embedding
    algorithm = param.algorithm
    quaternionic = param.quaternionic
    cohomological = param.cohomological

    if Up_method == "bigmatrix" and use_shapiro == True:
        import warnings
        warnings.warn('Use of "bigmatrix" for Up iteration is incompatible with Shapiro Lemma trick. Using "naive" method for Up.')
        Up_method = 'naive'

    if working_prec is None:
        working_prec = max([2 * prec + 10, 30])

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
    if quaternionic is None:
        quaternionic = ( DB != 1 )
    if cohomological is None:
        cohomological = quaternionic
    if quaternionic and not cohomological:
        raise ValueError("Need cohomological algorithm when dealing with quaternions")
    if use_ps_dists is None:
        use_ps_dists = False if cohomological else True
    try:
        p = ZZ(P)
    except TypeError:
        p = ZZ(P.norm())
    if not p.is_prime():
        raise ValueError,'P (= %s) should be a prime, of inertia degree 1'%P

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

    # Compute the completion of K at p
    x = QQ['x'].gen()
    K = F.extension(x*x - dK,names = 'alpha')
    if F == QQ:
        dK = K.discriminant()
    else:
        dK = K.relative_discriminant()

    hK = K.class_number()

    sgninfty = 'plus' if sign_at_infinity == 1 else 'minus'
    if hasattr(E,'cremona_label'):
        Ename = E.cremona_label()
    elif hasattr(E,'ainvs'):
        Ename = E.ainvs()
    else:
        Ename = 'unknown'
    fname = 'moments_%s_%s_%s_%s.sobj'%(P,Ename,sgninfty,prec)

    if use_sage_db:
        print "Moments will be stored in database as %s"%(fname)

    if outfile == 'log':
        outfile = '%s_%s_%s_%s_%s_%s.log'%(P,Ename,dK,sgninfty,prec,datetime.datetime.now().strftime("%Y%m%d-%H%M%S"))
        outfile = outfile.replace('/','div')
        outfile = '/tmp/darmonpoint_' + outfile

    fwrite("Starting computation of the Darmon point",outfile)
    fwrite('D_B = %s  %s'%(DB,factor(DB)),outfile)
    fwrite('Np = %s'%Np,outfile)
    fwrite('dK = %s (class number = %s)'%(dK,hK),outfile)
    fwrite('Calculation with p = %s and prec = %s'%(P,prec),outfile)
    fwrite('Elliptic curve %s: %s'%(Ename,E),outfile)
    if outfile is not None:
        print "Partial results will be saved in %s"%outfile

    if input_data is None:
        if cohomological:
            # Define the S-arithmetic group
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
            if F == QQ:
                abtuple = QuaternionAlgebra(DB).invariants()
            else:
                abtuple = quaternion_algebra_invariants_from_ramification(F, DB, ramification_at_infinity)

            G = BigArithGroup(P,abtuple,Np,base = F,outfile = outfile,seed = magma_seed,use_sage_db = use_sage_db,magma = magma, use_shapiro = use_shapiro)

            # Define the cycle ( in H_1(G,Div^0 Hp) )
            Coh = ArithCoh(G)
            while True:
                try:
                    cycleGn,nn,ell = construct_homology_cycle(G,beta,working_prec,lambda q: Coh.hecke_matrix(q).minpoly(), outfile = outfile, elliptic_curve = E)
                    break
                except PrecisionError:
                    working_prec *= 2
                    verbose('Encountered precision error, trying with higher precision (= %s)'%working_prec)
                except ValueError:
                    fwrite('ValueError occurred when constructing homology cycle. Returning the S-arithmetic group.', outfile)
                    if quit_when_done:
                        magma.quit()
                    return G
                except AssertionError as e:
                    fwrite('Assertion occurred when constructing homology cycle. Returning the S-arithmetic group.', outfile)
                    fwrite('%s'%str(e), outfile)
                    if quit_when_done:
                        magma.quit()
                    return G
            eisenstein_constant = -ZZ(E.reduction(ell).count_points())
            fwrite('r = %s, so a_r(E) - r - 1 = %s'%(ell,eisenstein_constant),outfile)
            fwrite('exponent = %s'%nn,outfile)
            phiE = Coh.get_cocycle_from_elliptic_curve(E, sign = sign_at_infinity)
            if hasattr(E,'ap'):
                sign_ap = E.ap(P)
            else:
                try:
                    sign_ap = ZZ(P.norm() + 1 - E.reduction(P).count_points())
                except ValueError:
                    from sage.schemes.plane_curves.constructor import Curve
                    sign_ap = ZZ(P.norm() + 1 - Curve(E).change_ring(P.residue_field()).count_points(1)[0])

            Phi = get_overconvergent_class_quaternionic(P,phiE,G,prec,sign_at_infinity,sign_ap,use_ps_dists = use_ps_dists,use_sage_db = use_sage_db,parallelize = parallelize,method = Up_method, progress_bar = progress_bar,Ename = Ename)
            # Integration with moments
            tot_time = walltime()
            J = integrate_H1(G,cycleGn,Phi,1,method = 'moments',prec = working_prec,parallelize = parallelize,twist = True,progress_bar = progress_bar)
            verbose('integration tot_time = %s'%walltime(tot_time))
            if use_sage_db:
                G.save_to_db()
        else: # not cohomological
            nn = 1
            eisenstein_constant = 1
            if algorithm is None:
                if Np == 1:
                    algorithm = 'darmon_pollack'
                else:
                    algorithm = 'guitart_masdeu'
            w = K.maximal_order().ring_generators()[0]
            r0,r1 = w.coordinates_in_terms_of_powers()(K.gen())
            QQp = Qp(p,working_prec)
            Cp = QQp.extension(w.minpoly().change_ring(QQp),names = 'g')
            v0 = K.hom([r0 + r1 * Cp.gen()])

            # Optimal embeddings of level one
            fwrite("Computing optimal embeddings of level one...", outfile)
            Wlist = find_optimal_embeddings(K,use_magma = use_magma, extra_conductor = extra_conductor)
            fwrite("Found %s such embeddings."%len(Wlist), outfile)
            if idx_embedding is not None:
                if idx_embedding >= len(Wlist):
                    fwrite('There are not enough embeddings. Taking the index modulo %s'%len(Wlist), outfile)
                    idx_embedding = idx_embedding % len(Wlist)
                fwrite('Taking only embedding number %s'%(idx_embedding), outfile)
                Wlist = [Wlist[idx_embedding]]

            # Find the orientations
            orients = K.maximal_order().ring_generators()[0].minpoly().roots(Zmod(Np),multiplicities = False)
            fwrite("Possible orientations: %s"%orients, outfile)
            if len(Wlist) == 1 or idx_orientation == -1:
                fwrite("Using all orientations, since hK = 1", outfile)
                chosen_orientation = None
            else:
                fwrite("Using orientation = %s"%orients[idx_orientation], outfile)
                chosen_orientation = orients[idx_orientation]

            emblist = []
            for i,W in enumerate(Wlist):
                tau, gtau,sign,limits = find_tau0_and_gtau(v0,Np,W,algorithm = algorithm,orientation = chosen_orientation,extra_conductor = extra_conductor)
                fwrite('n_evals = %s'%sum((num_evals(t1,t2) for t1,t2 in limits)), outfile)
                emblist.append((tau,gtau,sign,limits))

            # Get the cohomology class from E
            Phi = get_overconvergent_class_matrices(P,E,prec,sign_at_infinity,use_ps_dists = use_ps_dists,use_sage_db = use_sage_db,parallelize = parallelize,progress_bar = progress_bar)

            J = 1
            Jlist = []
            for i,emb in enumerate(emblist):
                fwrite("Computing %s-th period, attached to the embedding: %s"%(i,Wlist[i].list()), outfile)
                tau, gtau,sign,limits = emb
                n_evals = sum((num_evals(t1,t2) for t1,t2 in limits))
                fwrite("Computing one period...(total of %s evaluations)"%n_evals, outfile)
                newJ = prod((double_integral_zero_infty(Phi,t1,t2) for t1,t2 in limits))**ZZ(sign)
                Jlist.append(newJ)
                J *= newJ
    else: # input_data is not None
        Phi,J = input_data[1:3]
    fwrite('Integral done. Now trying to recognize the point', outfile)
    fwrite('J_psi = %s'%J,outfile)
    #Try to recognize a generator
    if quaternionic:
        local_embedding = G.base_ring_local_embedding(working_prec)
        twopowlist = [4, 3, 2, 1, 1/2, 3/2, 1/3, 2/3, 1/4, 3/4, 5/2, 4/3]
    else:
        local_embedding = Qp(p,working_prec)
        twopowlist = [4, 3, 2, 1, 1/2, 3/2, 1/3, 2/3, 1/4, 3/4, 5/2, 4/3]

    known_multiple = eisenstein_constant * nn
    while known_multiple % p == 0:
        known_multiple = ZZ(known_multiple / p)

    candidate,twopow,J1 = recognize_J(E,J,K,local_embedding = local_embedding,known_multiple = known_multiple,twopowlist = twopowlist,prec = prec, outfile = outfile)

    if candidate is not None:
        HCF = K.hilbert_class_field(names = 'r1') if hK > 1 else K
        if hK == 1:
            try:
                verbose('candidate = %s'%candidate)
                Ptsmall = E.change_ring(HCF)(candidate)
                fwrite('twopow = %s'%twopow,outfile)
                fwrite('Computed point:  %s * %s * %s'%(twopow,known_multiple,Ptsmall),outfile)
                fwrite('(first factor is not understood, second factor is)',outfile)
                fwrite('(r satisfies %s = 0)'%(Ptsmall[0].parent().gen().minpoly()),outfile)
                fwrite('================================================',outfile)
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
            if quit_when_done:
                magma.quit()
            return candidate
    else:
        fwrite('================================================',outfile)
        if quit_when_done:
            magma.quit()
        return []
