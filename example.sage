######################
# Parameters         #
######################

p= 13 # The prime
D = 2 * 3 # Discriminant of the quaternion algebra (even number of primes)
Np = 1 # Conductor of order. Currently only 1 is supported
dK = 5 # Calculate points on extensions of QQ(sqrt(dK))
prec = 20 # Precision to which result is desired

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

# Define the cycle ( in H_1(G,Div^0 Hp) )
cycleGn,nn,ell = G.construct_cycle(dK,prec,hecke_smoothen = True)


# Overconvergent lift
fname = '.moments_%s_%s_%s.sobj'%(p,D,prec)
if not os.path.isfile(fname):
    CohOC = CohomologyGroup(G.Gpn,overconvergent = True,base = Qp(p,prec))
    verbose('Computing moments...')
    VOC = CohOC.coefficient_module()
    PhiElift = CohOC([VOC(QQ(PhiE.evaluate(g)[0])).lift(M = prec) for g in G.Gpn.gens()])
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
