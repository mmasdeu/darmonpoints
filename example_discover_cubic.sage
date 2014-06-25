load('darmonpoints.sage')
from homology import lattice_homology_cycle
from integrals import integrate_H1
######################
# Parameters         #
######################

use_ps_dists = False
x = QQ['x'].gen()
F.<r> = NumberField(x^3-x^2-x+2)

NE = F.ideal(r^2 + 2)
P = NE.factor()[0][0]
D = NE/P
Np = NE/(P*D)
sign_at_infinity = 1 # Sign at infinity, can be +1 or -1
prec = 20 # Precision to which result is desired
working_prec = 50
outfile = 'points_%s_%s.txt'%(P,D)

verb_level = 1 # Set to 0 to remove output

# This function uses the elliptic curve, which we known.
# In the cases of interest, we just need a system of eigenvalues
def get_ap(p):
    E = EllipticCurve([-r-1,-r,-r-1,-r-1,0])
    F = E.base_ring()
    p = F.ideal(p)
    verbose('Called get_ap(p) with p = %s'%p)
    try:
        return E.reduction(p).trace_of_frobenius()
    except ValueError:
        Pnorm = p.norm()
        return ZZ(Pnorm + 1 - Curve(E.defining_polynomial().change_ring(F.residue_field(P))).count_points(1)[0])

#####################
# DO NOT EDIT BELOW #
#####################

# Set verbosity
set_verbose(verb_level)

# Define the S-arithmetic group
G = BigArithGroup(P,quaternion_algebra_from_discriminant(F,D).invariants(),Np,use_sage_db = False)

# Define PhiE, the cohomology class associated to the system of eigenvalues.
Coh = CohomologyGroup(G.Gpn)
PhiE = Coh.get_cocycle_from_elliptic_curve(get_ap,sign = sign_at_infinity)

g = G.Gn(G.Gpn.gen(2).quaternion_rep)
xi1, xi2 = lattice_homology_cycle(G,g,working_prec,outfile = outfile,method = 'short',few_integrals = True)

PhiElift = get_overconvergent_class_quaternionic(P,get_ap,G,prec,sign_at_infinity,use_ps_dists,apsign = get_ap(P),progress_bar = True)

qE1 = integrate_H1(G,xi1,PhiElift,1,method = 'moments',prec = working_prec, twist = False,progress_bar = True)
qE2 = integrate_H1(G,xi2,PhiElift,1,method = 'moments',prec = working_prec, twist = True,progress_bar = True)
qE = qE1/qE2

curve = discover_equation(qE,G._F_to_local,NE,prec).global_minimal_model()
