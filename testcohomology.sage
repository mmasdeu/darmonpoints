from darmonpoints.sarithgroup import BigArithGroup
from darmonpoints.cohomology_arithmetic import ArithCoh, get_twodim_cocycle, get_overconvergent_class_quaternionic


p = 11
D = 3 * 5
prec = 20
set_verbose(1)
magma.set_seed(123123)
G = BigArithGroup(p, D, 1, base=QQ, grouptype='SL2',magma=magma, use_shapiro=True)
Coh = ArithCoh(G)
V = Coh.space()