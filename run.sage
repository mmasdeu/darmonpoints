p= 13
D = 2 * 3
Np = 1
dK = 5
ell = 5
prec = 10
E = EllipticCurve(str(p*D*Np))
# P_E = E.base_extend(QuadraticField(dK,names = 'a')).lift_x(-2)
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

# Define the cycle ( in H_1(G,Div^0 Hp) )
cycleGn,nn = G.construct_cycle(dK,prec,hecke_smoothen = ell)

#############################################
# Overconvergent lift
VOC = CohOC.coefficient_module()
PhiElift = CohOC([VOC(QQ(PhiE.evaluate(g)[0])).lift(M = prec) for g in G.Gpn.gens()])
PhiElift = PhiElift.improve(prec = prec)
####################################################


###
# Integration with moments
tot_time = walltime()
J = integrate_H1(G,cycleGn,PhiElift,1,method = 'moments') # do not smoothen
print 'tot_time = %s'%walltime(tot_time)
print J
x,y = getcoords(E,J)
print x
## Should be 11 + 8*13 + 5*13^2 + 9*13^3 + 9*13^4 + 5*13^5 + 5*13^6 + 4*13^7 + 7*13^8 + 8*13^9 + O(13^10)

# Integration with Riemann sums
tot_time = walltime()
J = integrate_H1(G,cycleGn,PhiE,2,method = 'riemann') # do not smoothen
print 'tot_time = %s'%walltime(tot_time)
print J
x,y = getcoords(E,J)
print '------\n'
print x
## Should be 11 + 8*13 + 5*13^2 + 9*13^3 + 9*13^4 + 5*13^5 + 5*13^6 + 4*13^7 + 7*13^8 + 8*13^9 + O(13^10)

Jlog = J.log()
Cp = Jlog.parent()
addpart = Jlog/(2*nn)
for a,b in product(range(p),repeat = 2):
    if a == 0 and b == 0:
        continue
    multpart = Cp.teichmuller(a + Cp.gen()*b)
    J1 = multpart * addpart.exp()
    x,y = getcoords(E,J1)
    try:
        poly = algdep(x+O(p^17),2)
        print "%s,%s:\t(%s) %s"%(a,b,poly,poly.discriminant().squarefree_part())
    except PariError:
        continue

Jgood = addpart.exp()

## Check for multiples of P_E that agree
nP_E = P_E
for n in range(1,200):
    val = (x - QQ((nP_E)[0])).valuation()
    if val >= 2:
        print n,val
    if val > 10:
        break
    nP_E += P_E

# Measure tests
Up_reps = G.Gpn.get_Up_reps(p)
sj = Up_reps[2]
emb = G.get_embedding(prec)

# We get the corresponding open of Zp by looking at the opens given by BTreps
for i,e in enumerate(G.get_covering(1)):
    _,g,_ = list(e)
    pt1 = emb( g * sj**-1 ) * matrix(2,1,[0,1])
    pt2 = emb( sj * g**-1 ) * matrix(2,1,[0,1])
    val1 = (pt1[0,0]/pt1[1,0]).valuation()
    val2 = (pt2[0,0]/pt2[1,0]).valuation()
    if val1 >= 0 and val2 >= 0:
        print i,val1,val2
        res = e

a,b,c,d = emb(list(res)[1]**-1).list()
fd = lambda x: ((a*x+b)/(c*x+d))^3
cover = G.subdivide([res],3)
gamma = G.Gn.gen(2).quaternion_rep
hc = PhiE.shapiro_image(G)(gamma)
J = Qp(p,prec)(riemann_sum(G,fd,hc,cover = cover));print J

ti = G.Gn.get_hecke_ti(sj,gamma,p).quaternion_rep
J2 = PhiElift.shapiro_image(G)(ti)(BTEdge(False,G.get_BT_reps()[0],'even'))._moments[3]

# We test the measures directly
reps = G.get_BT_reps()
repshat = G.get_BT_reps_twisted()
edge0 =  G.get_covering(2)[42] #(1,repshat[5]*reps[3])
emb = G.get_embedding(prec)
a,b,c,d = emb(edge0[1]).list()
E0 = [edge0]
E1 = G.subdivide(E0,1)
E2 = G.subdivide(E0,2)
E3 = G.subdivide(E0,3)
E4 = G.subdivide(E0,4)
gamma =  G.Gn.gen(2).quaternion_rep # A "random" element in Gn
Cp.<s> = Qq(p^2)
R.<T> = PolynomialRing(Cp)
#fd = (T-s)/(T- (3+s+p*s + p*1))

fd = lambda x: ((a*x+b)/(c*x+d))^4 if x != Infinity else (a/c)^4
#fd = lambda x: x^3 if x != Infinity else 1
#fd = ((a*T+b)/(c*T+d))^3
val = riemann_sum(G,fd,PhiE.shapiro_image(G)(gamma),1,cover = E2); print val
# val = 11 + 5*13 + 7*13^2

# Now, with the overconvergent guy:
wp = G.wp
e0 = edge0[1]
val2 = PhiElift.shapiro_image(G)(gamma)(edge0)._moments[4] + O(p^5); print val2


btreps = G.get_BT_reps()
wp = G.wp
gvec = [g.quaternion_rep for g,v in cycle.get_data()]

hc = PhiE.shapiro_image(G)(gvec[0])

ebad = None
edgelist = G.get_covering(2)
for e in edgelist:
    subdiv = G.subdivide([e],1,1)
    mue = measure_test(G,hc,[e])
    print 'mue =', mue
    if mue != measure_test(G,hc,subdiv):
        print '!!'
        ebad = e
if ebad is None:
    print 'Great!'
else:
    print ':-('
    subdiv = G.subdivide([ebad],1,1)
    print [G.reduce_in_amalgam(e[1]) for e in subdiv]

# Test the sample points
level = 3
#edgelist = G.get_covering(level)
edgelist = G.get_covering(level)
v = []
vinf = []
for e in edgelist:
    te = sample_point(G,e,prec = 20)
    if te == Infinity:
        vinf.append(-1)
    elif te.valuation() < 0 :
        vinf.append(Zmod(p^(level))(-1/(p*te)))
    else:
        v.append(Zmod(p^level)(te).lift())
print factor(len(set(v)))
print factor(len(set(vinf)))

points_test(G,2)

# Test the BT reps
level = 1
reps = G.get_BT_reps()
v = []
vinf = []
emb = G.get_embedding(10)
for e in reps:
    a,b,c,d = emb(e**-1).list()
    if d == 0:
        vinf.append(-1)
    elif (b/d).valuation() < 0:
        vinf.append(-1)
    else:
        v.append(Zmod(p)(b/d).lift())
print factor(len(set(v)))
print factor(len(set(vinf)))

###### Test moment method (1) ################
depth = 3
g = G.Gpn.gen(3).quaternion_rep

emb = G.get_embedding(prec)
Cp =  cycleGn.parent().coefficient_module().base_ring()
K.<T> = PolynomialRing(Cp)
mom = 6
phi = T^mom

phi2 =  lambda t : phi(t)
cover = G.subdivide([BTEdge(False, 1)], 1, depth)

J1 = Cp(riemann_sum(G,phi2,PhiE.shapiro_image(G)(g),-1,cover))
print '..'
print J1 #11 + 4*13 + 2*13^2
J2 = PhiElift.evaluate(G.Gpn(g)).moment(mom) # (E.ap(5)-6) *
print '..'
print J2
print 'error:'
print J1-J2
print 'ratio:'
print J1/J2
##########################################


####################
g = (G.Gpn.gen(3)**-1*G.Gpn.gen(2)**2).quaternion_rep
emb = G.get_embedding(prec)
Upreps = G.Gpn.get_Up_reps()
Cp =  cycleGn.parent().coefficient_module().base_ring()
K.<T> = PolynomialRing(Cp)
mom = 2
phi = T**mom
R1.<r1> = LaurentSeriesRing(Cp)

J1 = PhiElift.evaluate(G.Gpn(g)).moment(mom)
print J1
J2 = 0
for j in range(p):
    sj = Upreps[j]
    a,b,c,d = emb(sj).list()
    tj = G.Gpn.get_hecke_ti(sj,g,p,reps = Upreps)
    mu_e = PhiElift.evaluate(G.Gpn(tj))
    pol = phi((R1(a)*r1+R1(b))/(R1(c)*r1+R1(d)))
    J2 += sum(Cp(a*mu_e.moment(i)) for a,i in izip(pol.coefficients(),pol.exponents()) if i < prec)
print '..'
print J2
print 'error:'
print J1-J2
print 'ratio:'
print J1/J2
##########################################


###### Test moment method (2) ################
j = 6
depth = 3
g = (G.Gpn.gen(3)**-1*G.Gpn.gen(2)**2).quaternion_rep

emb = G.get_embedding(prec)
Upreps = G.Gpn.get_Up_reps()
sj = Upreps[j]
Cp =  cycleGn.parent().coefficient_module().base_ring()
K.<T> = PolynomialRing(Cp)
phi = T**2

phi2 =  lambda t : phi(t)
cover = G.subdivide([BTEdge(True, G.get_BT_reps()[j+1])], 0, depth - 1)
J1 = Cp(riemann_sum(G,phi2,PhiE.shapiro_image(G)(g),-1,cover))
print '..'
print J1 #

a,b,c,d = emb(sj).list()
R1.<r1> = LaurentSeriesRing(Cp)
tj = G.Gpn.get_hecke_ti(sj,g,p,reps = Upreps)
mu_e = PhiElift.evaluate(G.Gpn(tj))
pol = phi((a*r1+b)/(c*r1+d))
J2 = sum(Cp(a*mu_e.moment(i)) for a,i in izip(pol.coefficients(),pol.exponents()) if i < prec)
print '..'
print J2
print 'error:'
print J1-J2
##########################################

###########
good_dK = []
for dK in range(1000,10000):
    if not is_fundamental_discriminant(dK):
        continue
    if kronecker_symbol(dK,2) != -1:
        continue
    if kronecker_symbol(dK,3) != -1:
        continue
    if kronecker_symbol(dK,13) != -1:
        continue
    good_dK.append(dK)

def is_good_K(D,p,DK):
	K=QuadraticField(DK)
	
	if all(K.ideal(q).is_prime() for q in D.prime_divisors()) and K.ideal(p).is_prime():
		return True
	else:	
		return False



#says true if -p has a square root in the algebra of discriminant D
def is_good_p(D,p):
	p1=D.factor()[0][0];p2=D.factor()[1][0]
	K=QuadraticField(-p)
	print K
	f1=K.ideal(p1).factor()
	f2=K.ideal(p2).factor()
	if len(f1)==1 and len(f2)==1 and f1[0][1]==1 and f2[0][1]==1:
		return True
	return False
