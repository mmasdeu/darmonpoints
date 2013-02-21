p= 13
D = 2*3
Np = 1
prec = 20
E = EllipticCurve(str(p*D*Np))
P_E = E.base_extend(QuadraticField(5,names = 'a')).lift_x(-2)
set_verbose(1)
total_magma_time = 0
G = BigArithGroup(p,D,Np)

# Test that coverings work
points_test(G,2)

# Calculate PhiE, the cohomology class associated to the curve E.
Coh = Cohomology(G.Gpn,0,overconvergent = False,base = Qp(p,prec))
CohOC = Cohomology(G.Gpn,0,overconvergent = True,base = Qp(p,prec))

# set_verbose(0)
# for l in [5,7,11,17]:
#     print l
#     print matrix(QQ,2,2,[o.rational_reconstruction() for o in Coh.hecke_matrix(l).list()])
#     print '--'
# set_verbose(1)
# print Coh.involution_at_infinity_matrix()
assert matrix(QQ,2,2,[o.rational_reconstruction() for o in Coh.hecke_matrix(p).list()]) == 1

# Apply t_r
#PhiE = Coh.apply_hecke_operator(Coh.gen(0),5) - Coh.gen(0).__rmul__(6)
PhiE = Coh.gen(0)

#############################################
# Overconvergent lift
VOC = CohOC.coefficient_module()
PhiElift = CohOC([VOC(b).lift(M = prec) for b in PhiE.values()])
PhiElift.improve()

####################################################
# Define the cycle ( in H_1(G,Div^0 Hp) )
cycle = G.embed_order(5,prec).hecke_smoothen(5)

# Integration with Riemann sums
tot_time = walltime()
J = integrate_H1(G,cycle,PhiE,3,method = 'riemann') #,smoothen_prime = 5)
print 'tot_time = %s'%walltime(tot_time)
print J
x,y = getcoords(E,J)
print x
## Should be 11 + 8*13 + 5*13^2 + O(13^3)

# Integration with moments
tot_time = walltime()
J = integrate_H1(G,cycle,PhiElift,1,method = 'moments',smoothen_prime = 5)
print 'tot_time = %s'%walltime(tot_time)
print J
x,y = getcoords(E,J)
print x
## Should be 11 + 8*13 + 5*13^2 + O(13^3)

## Check for multiples of P_E that agree
nP_E = P_E
for n in range(1,200):
    val = (x - QQ((nP_E)[0])).valuation()
    if val >= 2:
        print n,val
    if val > 10:
        break
    nP_E += P_E


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
    subdiv = G.subdivide([e],1)
    mue = measure_test(G,hc,[e])
    print 'mue =', mue
    if mue != measure_test(G,hc,subdiv):
        print '!!'
        ebad = e
if ebad is None:
    print 'Great!'
else:
    print ':-('
    subdiv = G.subdivide([ebad],1)
    print [G.reduce_in_amalgam(e[1]) for e in subdiv]

# Test the sample points
level = 2
edgelist = G.get_covering(level)
v = []
vinf = []
for e in edgelist:
    te = sample_point(G,e,prec = 20)
    if te == Infinity:
        print 'Infty'
    elif te.valuation() < 0 :
        vinf.append(Zmod(p^(level-1))(-1/(p*te)))
    else:
        v.append(Zmod(p^level)(te).lift())
print factor(len(set(v)))
print factor(len(set(vinf)))

points_test(G,3)
