p= 17
D = 1
Np = 1
disc = 5
prec = 20
E = EllipticCurve(str(p*D*Np))
F = QuadraticField(disc,names = 'a')
P_E = E.base_extend(F).lift_x(3)
set_verbose(1)
total_magma_time = 0
G = BigArithGroup(p,D,Np)

# Calculate PhiE, the cohomology class associated to the curve E.
Coh = Cohomology(G.Gpn,0,overconvergent = False, base = Qp(p,prec))
# Coh = Cohomology(G.Gpn,QQ^1)

r = 3

PhiE = Coh.gen(0)
# Coh.apply_hecke_operator(PhiE,r) - (r+1)*PhiE

h0 = G.embed_order(disc,20) #.hecke_smoothen(r)

depth = 2
## This should give us the Darmon (SH) point
tot_time = walltime()
J = integrate_H1(G,h0,PhiE,depth,method = 'riemann')
#J = integrate_H1(G,h0,PhiE,depth)
print 'tot_time = %s'%walltime(tot_time)
print J
x,y = getcoords(E,J)
print x

## Check for multiples of P_E that agree
nP_E = P_E
for n in range(1,20):
    val = (x - QQ((nP_E)[0])).valuation()
    if val >= 1:
        print n,val
    if val > 10:
        break
    nP_E += P_E
