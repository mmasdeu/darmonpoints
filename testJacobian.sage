### Init
from darmonpoints.schottky import *

# set_verbose(1)
p = 3
prec = 10
working_prec = 200
K = Qp(p,working_prec)#, print_mode='digits')
h1 = matrix(K, 2, 2, [-5,32,-8,35])
h2 = matrix(K, 2, 2, [-13,80,-8,43])
G = SchottkyGroup(K, (h1,h2))

### Naive periods
print('Computing naive periods')
t = cputime()
q00g = G.period_naive(0, 0, prec) # prec 21
q01g = G.period_naive(0, 1, prec) # prec 21
q11g = G.period_naive(1, 1, prec) # prec 21
print('Time = %.3f'%(cputime()-t))

### Overconvergent
print('Computing overconvergent periods')
z1 = G.a_point()
t = cputime()
q00 = G.period(0,0, prec, z1=z1)
q01 = G.period(0,1, prec, z1=z1)
q11 = G.period(1,1, prec, z1=z1)
print('Time = %.3f'%(cputime()-t))

print((q00g/q00-1).valuation())
print((q01g/q01-1).valuation())
print((q11g/q11-1).valuation())

