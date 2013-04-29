




#given p, D and a field K=Q(sqrt{DK}) says if K is valid or not
def is_good_K(D,p,DK):
	K=QuadraticField(DK)
	
	if all(K.ideal(q).is_prime() for q in D.prime_divisors()) and K.ideal(p).is_prime():
		return True
	else:	
		return False



#says true if p has a square root in the algebra of discriminant D
def is_good_p(D,p):
	p1=D.factor()[0][0];p2=D.factor()[1][0]
	K=QuadraticField(p)
	f1=K.ideal(p1).factor()
	f2=K.ideal(p2).factor()
	if len(f1)==1 and len(f2)==1 and f1[0][1]==1 and f2[0][1]==1:
		return True
	return False


#executar aquest bucle per trobar ternes [D,p,DK] valides (aqui D es el discriminant de l'algebra, p es el primer i DK el discriminant del cos). Una llista de ternes valides es aquesta:
good_D_p_DK=[[6, 5, 53], [6, 5, 77], [6, 5, 173], [6, 5, 197], [6, 29, 77], [6, 29, 101], [6, 53, 5], [6, 53, 101], [6, 53, 173], [6, 101, 29], [6, 101, 53], [6, 101, 149], [6, 101, 173], [6, 149, 77], [6, 149, 101], [6, 149, 197], [6, 173, 5], [6, 173, 53], [6, 173, 101], [6, 197, 5], [6, 197, 77], [6, 197, 149], [10, 13, 37], [10, 13, 93], [10, 13, 197], [10, 37, 13], [10, 37, 93], [10, 37, 133], [10, 53, 133], [10, 53, 157], [10, 53, 173], [10, 157, 53], [10, 157, 77], [10, 157, 133], [10, 173, 53], [10, 173, 93], [10, 197, 13], [10, 197, 77], [22, 13, 21], [22, 13, 85], [22, 13, 109], [22, 13, 149], [22, 13, 197], [22, 29, 21], [22, 29, 61], [22, 29, 85], [22, 29, 101], [22, 61, 21], [22, 61, 29], [22, 61, 85], [22, 61, 101], [22, 61, 173], [22, 101, 29], [22, 101, 61], [22, 101, 109], [22, 101, 149], [22, 101, 173], [22, 109, 13], [22, 109, 85], [22, 109, 101], [22, 109, 149], [22, 149, 13], [22, 149, 21], [22, 149, 101], [22, 149, 109], [22, 149, 197], [22, 173, 61], [22, 173, 101], [22, 197, 13], [22, 197, 21], [22, 197, 149]]
'''
good_D_p_DK=[]
for D in [6,10,22]:
	for p in prime_range(1,200):
		if not is_good_p(D,p):
			continue
		
		for DK in range(1,200):
			if not is_fundamental_discriminant(DK):
				continue
			if is_good_K(D,p,DK):
				good_D_p_DK.append([D,p,DK])

	
'''	
		
'''		
good_DK_30=[]
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

	


