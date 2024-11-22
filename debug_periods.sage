from darmonpoints.schottky import *

gens = load('gens.sobj')
K = gens[0].parent().base_ring()
# gens = [o.apply_map(lambda x : x.add_bigoh(20)) for o in gens]
W = SchottkyGroup(K,gens)
# W.balls()

W.period_matrix(20)

g1, g2 = gens
a = W.a_point()
Div = Divisors(a.parent())
Dg1 = Div([(1,a),(-1,act(g1,a))])
Dg2 = Div([(1,a),(-1,act(g2,a))])
Dg1 = W.find_equivalent_divisor(Dg1)
Dg2 = W.find_equivalent_divisor(Dg2)
T = W.theta(20, Dg1)
T(Dg1)
T(Dg2)

TT = W.theta(20, Dg2)
TT(Dg1)
