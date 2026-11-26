# Check the conversion of Magma ideals (order discriminant) to Sage.
from darmonpoints.sarithgroup import ArithGroup
from darmonpoints.util import magma_F_ideal_to_sage
F = QuadraticField(5, "r"); r = F.gen()
ab = (1/2*r + 1/2, F(-3))
P = F.ideal(3/2*r + 1/2)
G = ArithGroup(F, None, ab, P, magma=magma, backend="magma", grouptype="PSL2", compute_presentation=False)
D = G._O_magma.Discriminant()
print("magma disc:", D, "norm", D.Norm())
print("converted:", magma_F_ideal_to_sage(F, D, magma), "expected:", QuaternionAlgebra(F, *ab).discriminant() * P)
print("order_discriminant():", G.order_discriminant())
print("@@DONE@@")
