def is_good_K(p,D,DK):
	K=QuadraticField(DK)
	
	if all(K.ideal(q).is_prime() for q in D.prime_divisors()) and K.ideal(p).is_prime():
		return True
	else:	
		return False
'''
good_DK_30=[]
for DK in range(1,500):
	if not is_fundamental_discriminant(DK):
		continue
	if is_good_K(5,6,DK):
		good_DK_30.append(DK)

good_DK_42=[]
for DK in range(1,500):
	if not is_fundamental_discriminant(DK):
		continue
	if is_good_K(7,6,DK):
		good_DK_42.append(DK)

good_DK_78=[]
for DK in range(1,500):
	if not is_fundamental_discriminant(DK):
		continue
	if is_good_K(13,6,DK):
		good_DK_78.append(DK)
'''


#N=30
E30=EllipticCurve('30a1')
#real quadratic fields which meet the conditions (i.e. p is inert in K and all primes dividing D=6 are inert in K)
good_DK_30=[53, 77, 173, 197, 293, 317, 413, 437];

#we list the x_coordinates of points of infinite order of some of the real quadratic fields above
P_30_53=17/81
P_30_77=1411/448 
P_30_197=-23/121
P_30_437=-1783/2025

#N=42
E42=EllipticCurve('42a1')
good_DK_42=[5, 101, 173, 269, 293, 341, 437, 461];

K.<r>=QuadraticField(5)
P5=-6*r + 11

P_42_101=333797/30976

P_42_269=1357542722/11566801
P_42_342=6823/1859
p_42_437=60051/2783


#N=78
E78=EllipticCurve('78a1')
good_DK_78=[5, 149, 197, 293, 317, 437, 461];

P_78_5=-2
P_78_149=-482/49
P_78_197=142/25
P_78_293=40
P_78_317=382
P_78_437=-98/19
P_78_461=232

