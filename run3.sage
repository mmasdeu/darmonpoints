p= 17
D = 2 * 3
Np = 1
dK = 5
ell = 5
prec = 20
E = EllipticCurve(str(p*D*Np))
set_verbose(1)
G = BigArithGroup(p,D,Np)

# Calculate PhiE, the cohomology class associated to the curve E.
Coh = CohomologyTrivialCoeffs(G.Gpn,0,base = QQ)
CohOC = Cohomology(G.Gpn,0,overconvergent = True,base = Qp(p,prec))

n = 5
K1 = (Coh.hecke_matrix(n)-E.ap(n)).right_kernel()
assert K1.dimension() == 2
K2 = K1.intersection((Coh.involution_at_infinity_matrix()-1).right_kernel())
assert K2.dimension() == 1
col = [ZZ(o) for o in K2.matrix().list()]

PhiE = Coh.construct_element_from_vector(col)

# Define the cycle ( in H_1(G,Div^0 Hp) )
cycleGn,nn = G.construct_cycle(dK,prec,hecke_smoothen = ell)

#############################################
# Overconvergent lift
VOC = CohOC.coefficient_module()
PhiElift = CohOC([VOC(QQ(PhiE.evaluate(g)[0])).lift(M = prec) for g in G.Gpn.gens()])
PhiElift = PhiElift.improve(prec = prec,sign = -E.ap(p))
####################################################


###
# Integration with moments
tot_time = walltime()
J = integrate_H1(G,cycleGn,PhiElift,1,method = 'moments') # do not smoothen
print 'tot_time = %s'%walltime(tot_time)
print J
x,y = getcoords(E,J,prec)
print x
##

# Integration with Riemann sums
tot_time = walltime()
J = integrate_H1(G,cycleGn,PhiE,2,method = 'riemann') # do not smoothen
print 'tot_time = %s'%walltime(tot_time)
print J
x,y = getcoords(E,J,prec)
print '------\n'
print x
##

Jlog = J.log()
Cp = Jlog.parent()
addpart = Jlog/(2*nn)
for a,b in product(range(p),repeat = 2):
    if a == 0 and b == 0:
        continue
    # print a,b
    multpart = Cp.teichmuller(a + Cp.gen()*b)
    J1 = multpart * addpart.exp()
    x,y = getcoords(E,J1,prec)
    try:
        poly = algdep(x.trace()+O(p^(prec)),1)
        #print factor(poly)
        print "%s,%s:\t(%s) %s"%(a,b,poly,poly.discriminant().squarefree_part())
        poly = algdep(x.norm()+O(p^(prec)),1)
        #print factor(poly)
        print "%s,%s:\t(%s) %s"%(a,b,poly,poly.discriminant().squarefree_part())
    except (KeyboardInterrupt,PariError):
        continue

a, b = 1,6
multpart = Cp.teichmuller(a + Cp.gen()*b)
Jgood = multpart * addpart.exp()
x,y = getcoords(E,Jgood,prec)
EK = E.base_extend(QuadraticField(dK,names='r'))
Pgood = EK.lift_x(algdep(x+O(p^prec),1).roots(QQ)[0][0])

## Check for multiples of P_E that agree
nP_E = P_E
for n in range(1,200):
    val = (x - QQ((nP_E)[0])).valuation()
    if val >= 2:
        print n,val
    if val > 10:
        break
    nP_E += P_E
