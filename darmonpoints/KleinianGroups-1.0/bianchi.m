/*

bianchi.m
functions for handling Bianchi groups

bianchi.m is part of KleinianGroups, version 1.0 of September 25, 2012
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/

intrinsic BianchiOrder(d :: RngIntElt) -> AlgAssVOrd
{
    An order O in a quaternion algebra such that the norm one group is the Bianchi group of Q(sqrt(-|d|)).
}

	R<x> := PolynomialRing(Rationals());
    d := Abs(d);
	K<alpha> := NumberField(x^2+d);
	ZK := MaximalOrder(K);
	
	B := QuaternionAlgebra<K|1,1>;
	O := Order([One(B),(One(B)+B.1)/2,(B.2+B.3)/2,(B.2-B.3)/2]);
	
	return O;
end intrinsic;

function QuatToMatrix(g)
	K := BaseField(Parent(g));
	return MatrixRing(K,2) ! [g[1]+g[2],g[3]+g[4],g[3]-g[4],g[1]-g[2]];
end function;

function MatrixToQuat(m,O)
	B<i,j,k> := Algebra(O);
	return (m[1,1]*(1+i)+m[2,2]*(1-i)+m[1,2]*(j+k)+m[2,1]*(j-k))/2;
end function;
