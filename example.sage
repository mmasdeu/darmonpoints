######################
# Parameters         #
######################

p= 13 # The prime
D = 2 * 3 # Discriminant of the quaternion algebra (even number of primes)
Np = 1 # Conductor of order. Currently only 1 is supported
# dK = 5 # Calculate points on extensions of QQ(sqrt(dK))
dKlist = [ 5 ]

# 5, 149, 197, 293, 317, 437, 461, 509, 557
# [10, 18*r - 5, 1]
# [-10654790/1138489, 1229396070/1214767763*r + 5327395/1138489, 1]
# [964090/121), -67449270/1331*r - 482045/121, 1]
# [66626/7325, -23188374/10731125*r - 33313/7325, 1]
# [36974414/388325, -226154303712/4308465875*r - 18487207/388325, 1]
# [971110/339889, -244302600/198155287*r - 485555/339889, 1]
# [-146849210/23609881, 132062657760/114720411779*r + 73424605/23609881, 1]
# [86626030090/4613262241, -1193915313019350/313337384670961*r - 43313015045/4613262241, 1]
# [394312144429886/2528440578125, 7858947314645355852384/94887001960802734375*r - 197156072214943/2528440578125, 1]
prec = 19 # Precision to which result is desired

verb_level = 1 # Set to 0 to remove output

# We will find points on the elliptic curve of conductor p*D*Np

#####################
# DO NOT EDIT BELOW #
#####################

# Set verbosity
set_verbose(verb_level)

# Define the elliptic curve
E = EllipticCurve(str(p*D*Np))

# Define the S-arithmetic group
G = BigArithGroup(p,D,Np)

# Define PhiE, the cohomology class associated to the curve E.
Coh = CohomologyGroup(G.Gpn)
PhiE = Coh.get_cocycle_from_elliptic_curve(E,sign = 1)

for dK in dKlist:
    # Define the cycle ( in H_1(G,Div^0 Hp) )
    cycleGn,nn,ell = G.construct_cycle(dK,prec,hecke_smoothen = True)


    # Overconvergent lift
    fname = '.moments_%s_%s_%s.sobj'%(p,D,prec)
    if not os.path.isfile(fname):
        CohOC = CohomologyGroup(G.Gpn,overconvergent = True,base = Qp(p,prec))
        verbose('Computing moments...')
        VOC = CohOC.coefficient_module()
        if use_ps_dists:
            PhiElift = CohOC([VOC(QQ(PhiE.evaluate(g)[0])).lift(M = prec) for g in G.Gpn.gens()])
        else:
            PhiElift = CohOC([VOC(Matrix(VOC._R,VOC._depth,1,[PhiE.evaluate(g)[0]]+[0 for i in range(VOC._depth - 1)])) for g in G.Gpn.gens()])
        PhiElift = PhiElift.improve(prec = prec,sign = E.ap(p))
        save(PhiElift._val,fname)
        verbose('Done.')
    else:
        verbose('Using precomputed moments')
        Phivals = load(fname)
        CohOC = CohomologyGroup(G.Gpn,overconvergent = True,base = Qp(p,prec))
        CohOC._coeff_module = Phivals[0].parent()
        VOC = CohOC.coefficient_module()
        PhiElift = CohOC([VOC(o) for o in Phivals])

    # Integration with moments
    tot_time = walltime()
    J = integrate_H1(G,cycleGn,PhiElift,1,method = 'moments') # do not smoothen
    verbose('integration tot_time = %s'%walltime(tot_time))
    x,y = getcoords(E,J,prec)

    # Try to recognize the point
    set_verbose(0)
    F.<r> = QuadraticField(dK)
    Jlog = J.log()
    Cp = Jlog.parent()
    addpart = (2*Jlog)/((E.ap(ell) - (ell+1))*nn)
    candidate = None
    for a,b in product(range(p),repeat = 2):
        if a == 0 and b == 0:
            continue
        # print a,b
        multpart = Cp.teichmuller(a + Cp.gen()*b)
        J1 = multpart * addpart.exp()
        if J1 == Cp(1):
            candidate = E(0)
            verbose('Recognized the point, it is zero!')
            break
        else:
            x,y = getcoords(E,J1,prec)
            success = False
            prec0 = prec
            while not success and prec0 > prec-5:
                verbose('Trying to recognize point with precision %s'%prec0, level = 2)
                candidate,success = recognize_point(x,y,E.change_ring(F),prec = prec0)
                prec0 -= 1
            if not success:
                verbose('Could not recognize point',level = 2)
                continue
            verbose('Recognized the point!')
            break
    set_verbose(verb_level)
    print 'Here is the candidate point:'
    print candidate
