p= 13
D = 2*3
Np = 1
prec = 20
E = EllipticCurve(str(p*D*Np))
P_E = E.base_extend(QuadraticField(5,names = 'a')).lift_x(-2)
set_verbose(1)
total_magma_time = 0
G = BigArithGroup(p,D,Np)

# Calculate PhiE, the cohomology class associated to the curve E.
Coh = Cohomology(G.Gpn,0,overconvergent = False,base = Qp(p,prec))
CohOC = Cohomology(G.Gpn,0,overconvergent = True,base = Qp(p,prec))

# set_verbose(1)
# for l in [7,11,17]:
#     print l
#     print matrix(QQ,2,2,[o.rational_reconstruction() for o in Coh.hecke_matrix(l).list()])
#     print '--'
# set_verbose(1)
# print Coh.involution_at_infinity_matrix()
# print Coh.hecke_matrix(p)

PhiE = Coh.gen(0)
VOC = CohOC.coefficient_module()
PhiElift = CohOC([VOC(b).lift(M = prec) for b in PhiE.values()])
PhiElift.improve()

####################################################
h = G.embed_order(5,prec).hecke_smoothen(5)

level = 1
total_magma_time = 0
tot_time = walltime()
J = integrate_H1(G,h,PhiElift,level,method = 'moments')
print 'tot_time = %s'%walltime(tot_time)
print J
x,y = getcoords(E,J)
print x
## Should be 11 + 8*13 + 5*13^2 + O(13^3)


## Check for multiples of P_E that agree
nP_E = P_E
for n in range(1,100):
    val = (x - QQ((nP_E)[0])).valuation()
    if val >= 1:
        print n,val
    if val > 10:
        break
    nP_E += P_E


btreps = G.get_BT_reps()
wp = G.wp
gvec = [g.quaternion_rep for g,v in h0.get_data()]
hc = PhiE(gvec[0])

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

points_test(G,level)
