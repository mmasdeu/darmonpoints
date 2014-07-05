load('darmonpoints.sage')
from homology import lattice_homology_cycle,lattice_homology_cycle_new
from integrals import integrate_H1
######################
# Parameters         #
######################
use_ps_dists = False
p = 5 # The prime
D = 2 * 3 # Discriminant of the quaternion algebra (even number of primes)
Np = 1 # Conductor of order.
sign_at_infinity = 1 # Sign at infinity, can be +1 or -1
prec = 50 # Precision to which result is desired
working_prec = 100
outfile = 'points_%s_%s.txt'%(p,D)

verb_level = 1 # Set to 0 to remove output
#####################
# DO NOT EDIT BELOW #
#####################

# Set verbosity
set_verbose(verb_level)

# Define the elliptic curve
E = EllipticCurve(str(p*D*Np))

# Define the S-arithmetic group
G = BigArithGroup(p,quaternion_algebra_from_discriminant(QQ,D).invariants(),Np,use_sage_db = False)

PhiElift = get_overconvergent_class_quaternionic(p,E,G,prec,sign_at_infinity,use_ps_dists,progress_bar = True)

# This has been found by hand
g =  G.Gn(G.Gpn.gen(1).quaternion_rep)

#xi1, xi2 = lattice_homology_cycle(G,g,working_prec, outfile = outfile,method = 'short',few_integrals = True)
xi1,xi2 = lattice_homology_cycle_new(G,g,working_prec)

qE1 = integrate_H1(G,xi1,PhiElift,1,method = 'moments',twist = False,progress_bar = True)
qE2 = integrate_H1(G,xi2,PhiElift,1,method = 'moments',twist = True,progress_bar = True)
qE = qE1/qE2

f = QQ.hom([Qp(p,prec)(1)])
E = discover_equation(qE,f,p*D*Np,prec).minimal_model()
