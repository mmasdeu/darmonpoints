

# This file was *autogenerated* from the file testJacobian.sage
from sage.all_cmdline import *   # import sage library

_sage_const_3 = Integer(3); _sage_const_10 = Integer(10); _sage_const_200 = Integer(200); _sage_const_2 = Integer(2); _sage_const_5 = Integer(5); _sage_const_32 = Integer(32); _sage_const_8 = Integer(8); _sage_const_35 = Integer(35); _sage_const_13 = Integer(13); _sage_const_80 = Integer(80); _sage_const_43 = Integer(43); _sage_const_4 = Integer(4); _sage_const_20 = Integer(20); _sage_const_0 = Integer(0); _sage_const_1 = Integer(1)### Init
from darmonpoints.schottky import *

# set_verbose(1)
p = _sage_const_3 
prec = _sage_const_10 
working_prec = _sage_const_200 
K = Qp(p,working_prec)#, print_mode='digits')
h1 = matrix(K, _sage_const_2 , _sage_const_2 , [-_sage_const_5 ,_sage_const_32 ,-_sage_const_8 ,_sage_const_35 ])
h2 = matrix(K, _sage_const_2 , _sage_const_2 , [-_sage_const_13 ,_sage_const_80 ,-_sage_const_8 ,_sage_const_43 ])
G = SchottkyGroup(K, (h1,h2))

for prec in range(_sage_const_4 ,_sage_const_20 ):
    print(f'{prec =}', end = ' ')
    ### Naive periods
    # print('Computing naive periods')
    t = cputime()
    q00g = G.period_naive(_sage_const_0 , _sage_const_0 , prec) # prec 21
    # q01g = G.period_naive(0, 1, prec) # prec 21
    # q11g = G.period_naive(1, 1, prec) # prec 21
    print('Time = %.3f'%(cputime()-t), end = ' ')

    ### Overconvergent
    # print('Computing overconvergent periods')
    z1 = G.a_point()
    t = cputime()
    q00 = G.period(_sage_const_0 ,_sage_const_0 , prec, z1=z1)
    # q01 = G.period(0,1, prec, z1=z1)
    # q11 = G.period(1,1, prec, z1=z1)
    print('Time = %.3f'%(cputime()-t), end = ' ')

    print((q00g/q00-_sage_const_1 ).valuation())
    # print((q01g/q01-1).valuation())
    # print((q11g/q11-1).valuation())



