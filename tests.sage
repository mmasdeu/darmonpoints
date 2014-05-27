load('darmonpoints.sage')
from homology import lattice_homology_cycle
from integrals import integrate_H1
######################
# Parameters         #
######################
use_ps_dists = False
p = 5 # The prime
D = 2 * 3 # Discriminant of the quaternion algebra (even number of primes)
Np = 1 # Conductor of order.
sign_at_infinity = 1 # Sign at infinity, can be +1 or -1
prec = 20 # Precision to which result is desired
working_prec = 50
outfile = 'points_%s_%s.txt'%(p,D)

verb_level = 1 # Set to 0 to remove output

# We will find points on the elliptic curve of conductor p*D*Np
dK = 53
#####################
# DO NOT EDIT BELOW #
#####################

# Set verbosity
set_verbose(verb_level)

# Define the elliptic curve
E = EllipticCurve(str(p*D*Np))

# Define the S-arithmetic group
G = BigArithGroup(p,quaternion_algebra_from_discriminant(QQ,D).invariants(),Np,use_sage_db = False)

# Define PhiE, the cohomology class associated to the curve E.
Coh = CohomologyGroup(G.Gpn)
PhiE = Coh.get_cocycle_from_elliptic_curve(E,sign = sign_at_infinity)

A = G.Gpn.hecke_matrix(17)
print A
assert E.ap(17) in A.eigenvalues()

g =  G.Gpn.gen(1)

from homology import Homology
W = (g**12).find_bounding_cycle(G)
HomGn = Homology(G.Gn,ZZ)
ans = HomGn(dict([(G.Gn(g.quaternion_rep)**12,-1)]))
for n,x,y in W:
    if n == 1:
        ans = ans + HomGn(x) + HomGn(y) - HomGn(x*y)
    else:
        assert n == -1
        ans = ans - HomGn(x) - HomGn(y) + HomGn(x*y)
print ans

wp = G.wp
W1 = G.Gn((g.quaternion_rep**12)).find_bounding_cycle(G)
W2 = G.Gn(wp**-1 * (g.quaternion_rep**12) * wp).find_bounding_cycle(G)
HomGn = Homology(G.Gn.B,ZZ)
ans = HomGn(dict([]))
for n,x,y in W1:
    xh = x.quaternion_rep
    yh = y.quaternion_rep
    if n == 1:
        ans = ans + (HomGn(xh) + HomGn(yh) - HomGn(xh*yh))
    else:
        assert n == -1
        ans = ans - (HomGn(xh) + HomGn(yh) - HomGn(xh*yh))
for n,x,y in W2:
    xh = wp * x.quaternion_rep * wp**-1
    yh = wp * y.quaternion_rep * wp**-1
    if n == 1:
        ans = ans -( HomGn(xh) + HomGn(yh) - HomGn(xh*yh))
    else:
        assert n == -1
        ans = ans +( HomGn(xh) + HomGn(yh) - HomGn(xh*yh))

assert E.ap(11) * G.Gpn.image_in_abelianized(g) == G.Gpn.act_by_hecke(11,g)
xi1, xi2 = lattice_homology_cycle(G,g,working_prec,hecke_smoothen = True, outfile = outfile)

Div = xi1[0][1].parent()
tmp = Div([])
Cp = xi1[0][1].parent().base_ring()
for y,D in xi1:
    a,b,c,d = G.embed(y.quaternion_rep**-1,working_prec).change_ring(Cp).list()
    mat = G.embed(y.quaternion_rep**-1,working_prec).change_ring(Cp)
    tmp += D.left_act_by_matrix(mat) - D
    # for P,n in D:
    #     tmp += n*(a*P+b)/(c*P+d) - n*P
for y,D in xi2:
    a,b,c,d = G.embed(G.wp * y.quaternion_rep**-1 * G.wp**-1,working_prec).change_ring(Cp).list()
    mat = G.embed(G.wp * y.quaternion_rep**-1 * G.wp**-1,working_prec).change_ring(Cp)
    aw,bw,cw,dw = G.embed(G.wp,working_prec).change_ring(Cp).list()
    wpm = G.embed(G.wp,working_prec).change_ring(Cp)
    tmp -= (D.left_act_by_matrix(wpm)).left_act_by_matrix(mat) - D.left_act_by_matrix(wpm)
    # for P,n in D:
    #     wP = (aw*P+bw)/(cw*P+dw)
    #     tmp -= n*(a*wP+b)/(c*wP+d) - n*wP



ans1 = xi1._check_cycle_condition(True)[1]
ans2 = xi2._check_cycle_condition(True)[1]
ans2t = ans2.left_act_by_matrix(G.embed(G.wp,working_prec))
ans3 = ans1 - ans2t
for P,n in ans3:
    print n

PhiElift = get_overconvergent_class_quaternionic(p,E,G,prec,sign_at_infinity,use_ps_dists)

qE2 = integrate_H1(G,xi2,PhiElift,1,method = 'moments',twist=True)
qE1 = integrate_H1(G,xi1,PhiElift,1,method = 'moments',twist=False)

qE = qE1/qE2
from util import get_c4_and_c6
c4, c6 = get_c4_and_c6(qE,prec)
DeltaE = (c4**3-c6**2)/1728
jE = (c4**3)/DeltaE
qEgood = E.tate_curve(p).parameter()
c4g,c6g = get_c4_and_c6(qEgood,prec)
DeltaEg = (c4g**3-c6g**2)/1728
jEg = (c4g**3)/DeltaEg

res = xi1.parent().coefficient_module()(0)
for g,v in xi1._data.iteritems():
    res += (g**-1) * v - v
for g,v in xi2._data.iteritems():
    res -= ((g**-1)*v - v).left_act_by_matrix(G.embed(G.wp,prec))
