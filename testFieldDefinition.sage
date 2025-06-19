### Init
from darmonpoints.schottky import *

# set_verbose(1)
p = 3
prec = 20
working_prec = 200
K.<a> = Qq(p**2,working_prec)#, print_mode='digits')
h1 = matrix(K, 2, 2, [-5,32,-8,35])
h2 = matrix(K, 2, 2, [-13,80,-8,43])
G = SchottkyGroup(K, (h1,h2))
Th = G.theta(prec, 0, 2*3^-1, improve=True) # Can't use 1, because it's a limit point

how_padic = lambda x : x._flint_rep_abs()[0][1].valuation(p)

# The following illustrates how elements in Qp (like w) do not lift to elements in Qp
z = 1 + a*3^2 + 2*3^3 + (a + 2)*3^4 + (a + 2)*3^5 + (a + 2)*3^6 + a*3^7 + (a + 1)*3^8 + 2*a*3^9 + a*3^11 + 2*a*3^13 + 2*3^14 + 2*3^17 + 3^18 + 3^19 + 2*3^20 + (2*a + 2)*3^21
w = Th(z) # w = 3 + 2*3^3 + 3^5 + 2*3^7 + 3^8 + 2*3^10 + 2*3^12 + 2*3^14 + 2*3^15 + 2*3^20 + O(3^21)




while True:
    z0 = K.random_element().unit_part()
    z1 = z + z0*3**14
    w = Th(z1)
    if how_padic(w) > 20:
        print(z1)
        print(w)
        break

w = Th(z) # w = 3^2 + 2*3^4 + 3^5 + 3^6 + 2*3^7 + 2*3^8 + 3^10 + 3^11 + 3^12 + 3^13 + 2*3^14 + 2*3^15 + 3^16 + 3^17 + 2*3^19 + O(3^22)
