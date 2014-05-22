load('darmonpoints.sage')
from homology import lattice_homology_cycle
from integrals import integrate_H1
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
G = BigArithGroup(p,D,Np,use_sage_db = False)

# Define PhiE, the cohomology class associated to the curve E.
Coh = CohomologyGroup(G.Gpn)
PhiE = Coh.get_cocycle_from_elliptic_curve(E,sign = sign_at_infinity)

A = G.Gpn.hecke_matrix(17)
print A
assert E.ap(17) in A.eigenvalues()

g =  G.Gpn.gen(1)

from homology import Homology
W = (g**3).find_bounding_cycle(G)
HomGn = Homology(G.Gn,ZZ)
ans = HomGn(dict())
for n,x,y in W:
    if n == 1:
        ans = ans + HomGn(x) + HomGn(y) - HomGn(x*y)
    else:
        assert n == -1
        ans = ans - HomGn(x) - HomGn(y) + HomGn(x*y)
ans = ans - HomGn(g**3)

assert E.ap(11) * G.Gpn.image_in_abelianized(g) == G.Gpn.act_by_hecke(11,g)
xi1,xi2 = lattice_homology_cycle(G,g,prec,outfile)

PhiElift = get_overconvergent_class_quaternionic(p,E,G,prec,sign_at_infinity,use_ps_dists)

qE1 = integrate_H1(G,xi1,PhiElift,1,method = 'moments')
qE2 = integrate_H1(G,xi2,PhiElift,1,method = 'moments',twist= True)
qE = qE1/qE2
from util import get_c4_and_c6
c4, c6 = get_c4_and_c6(qE,prec)
DeltaE = (c4**3-c6**2)/1728
jE = (c4**3)/DeltaE
qEgood = E.tate_curve(p).parameter()
c4g,c6g = get_c4_and_c6(qEgood,prec)
DeltaEg = (c4g**3-c6g**2)/1728
jEg = (c4g**3)/DeltaEg
