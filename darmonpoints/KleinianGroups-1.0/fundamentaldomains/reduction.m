/*

reduction.m
functions implementing reduction algorithms for exterior domains

reduction.m is part of KleinianGroups, version 0.1 of May 20, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../geometry/basics.m" : Delta, action, sqrnorm, JtoP;
import "../aux.m" : epsilon;
import "../kleinian.m" : kleinianmatrix, epsdef;
import "normalizedbasis.m" : CheckTimeOut;

intrinsic GetMatrixList(Boundary :: SeqEnum) -> SeqEnum
{
Returns the list of matrices in a way that is usable by Sage
}
    n := #Boundary;
    newlist := [];
    for i := 1 to n do
        mat := Boundary[i]`Matrix;
        Append(~newlist, [mat[1,1],mat[1,2],mat[2,1],mat[2,2]]);
    end for;
    return newlist;
end intrinsic;

intrinsic GetPandPinv(B :: AlgQuat ) -> AlgMatElt,AlgMatElt
{
Returns the P and Pinv matrices
}
    H := B`KlnH;
    pr := Precision(BaseField(H));
    Center := H.2;
    M:=MatrixRing(ComplexField(pr),2);
    return JtoP(Center,M);

end intrinsic;

intrinsic ReducePoint(z :: AlgQuatElt, Boundary :: SeqEnum : eps12 := epsdef, DontUse := {}, Word := true, Evaluate := true) -> AlgQuatElt,SeqEnum,AlgQuatElt, RngIntElt
{
    Computes a point in the exterior domain with faces Boundary that is equivalent to z. Returns the equivalent point, the element delta such that delta*z is reduced as a word and as a quaternion, and the length of the reduction.
}
	H := Parent(z);
	R := BaseField(H);
	
	Rpr := RealField(10);
	n := #Boundary;
	error if n eq 0, "Empty boundary";
	B := Parent(Boundary[1]`g);
	reduced := false;
	deltaword := [];
	lengthw := 0;
	delta := B!1;
	
	while not reduced do
		i0 := 0;
        d := R!1;
		for i := 1 to n do
			   //CheckTimeOut();
			if not (Boundary[i]`g in DontUse) then
                d1 := sqrnorm(z - Boundary[i]`Center)/(Boundary[i]`Radius)^2;
				if d ge (1+eps12)*d1 then
					d := d1;
					i0 := i;
				end if;
			end if;
		end for;
		
		if i0 eq 0 then
			reduced := true;
		else
		    z := action(Boundary[i0]`Matrix,z);
			if Word then
				Append(~deltaword,i0);
			end if;
			if Evaluate then
				delta := (Boundary[i0]`g)*delta;
			end if;
			lengthw +:= 1;
            if not Word and Trace(Boundary[i0]`g)^2 eq 4*Norm(Boundary[i0]`g) then
                gg := Boundary[i0]`g;
                zz := z;
                help := -1;
                repeat
                    help +:= 1;
                    z := zz;
                    gg := gg^2;
                    zz := action(kleinianmatrix(gg),z);
                    delta := gg * delta;
                until Delta(z,H!0) le (1+eps12)*Delta(zz,H!0);
                delta := gg^(-1)*delta;
            end if;
		end if;
		
	end while;
	
	Reverse(~deltaword);
	return z,deltaword,delta,lengthw; //Red(z) = delta*z, deltaword evaluates to delta.
end intrinsic;

intrinsic Reduce(gamma :: AlgQuatElt, Boundary :: SeqEnum : eps12 := epsdef, z := (Parent(gamma)`KlnH)!0, DontUse := {}, Word := true, Evaluate := true) -> SeqEnum,AlgQuatElt,AlgQuatElt, RngIntElt //Red(gamma) = delta*gamma, deltaword evaluates to delta.
{
    Computes the reduction of gamma with respect to the exterior domain with faces Boundary. Returns the element delta such that delta*gamma*z is in the exterior domain as a word and as a quaternion, the reduced point, and the length of the reduction
}
	z,deltaword,delta,length := ReducePoint(action((kleinianmatrix(gamma)) , z), Boundary : eps12 := eps12, DontUse := DontUse, Word := Word, Evaluate := Evaluate);
	return deltaword,delta,z,length;
end intrinsic;

intrinsic Word(gamma :: AlgQuatElt, Boundary :: SeqEnum, G :: GrpFP) -> GrpFPElt
{
    Returns the element in the finitely presented group G corresponding to the quaternion gamma. 
}
    R := Parent(Boundary[1]`Radius);
    eps := epsilon(1/2,Precision(R));
    word := Reduce(gamma^(-1), Boundary : eps12 := eps, Evaluate := false);
    g := One(G);
    for i := 1 to #word do
        g := g*G.(word[i]);
    end for;
    return g;
end intrinsic;

