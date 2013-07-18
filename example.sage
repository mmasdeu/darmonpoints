######################
# Parameters         #
######################
use_ps_dists = False
p = 13 # The prime
D = 2 * 3 # Discriminant of the quaternion algebra (even number of primes)
Np = 1 # Conductor of order.
sign_at_infinity = 1 # Sign at infinity, can be +1 or -1
prec = 20 # Precision to which result is desired
outfile = 'points_%s_%s.txt'%(p,D)

verb_level = 1 # Set to 0 to remove output

# We will find points on the elliptic curve of conductor p*D*Np
dK = 5
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
PhiE = Coh.get_cocycle_from_elliptic_curve(E,sign = sign_at_infinity)

# Define the cycle ( in H_1(G,Div^0 Hp) )
cycleGn,nn,ell = G.construct_cycle(dK,prec,hecke_smoothen = True)

PhiElift = get_overconvergent_class_quaternionic(p,E,G,prec,sign_at_infinity,use_ps_dists)

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
smoothen_constant = ZZ(E.ap(ell) - (ell+1))
while smoothen_constant % p == 0 :
    smoothen_constant = ZZ(smoothen_constant / p)
addpart = (2*Jlog)/(smoothen_constant*nn)
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
        while not success and 2 * prec0 > prec:
            verbose('Trying to recognize point with precision %s'%prec0, level = 2)
            candidate,success = recognize_point(x,y,E.change_ring(F),prec = prec0)
            prec0 -= 1
        if not success:
            verbose('Could not recognize point',level = 2)
            continue
        verbose('Recognized the point!')
        break
set_verbose(verb_level)
if success:
    print 'Here is the candidate point:'
    print candidate
else:
    print 'No success this time...'
