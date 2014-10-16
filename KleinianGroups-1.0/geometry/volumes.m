/*

volumes.m
functions for computing hyperbolic volumes and areas

volumes.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../aux.m" : epsilon;
import "basics.m" : sqrnorm, scalar, PointsToSphere, PerturbatedBtoH, IntersectionAngle, EndPoints;

function VolumeDisc(r)
 R := Parent(r);
 return 2*Pi(R)*(Cosh(r)-1);
end function;

function VolumeBall(r)
 R := Parent(r);
 return Pi(R)*(Sinh(2*r)-2*r);
end function;

function dVolumeBall(r)
 R := Parent(r);
 return 2*Pi(R)*(Cosh(2*r)-1);
end function;

/*
    Precomputes the coefficients of the power series expansion of the Lobachevsky function. Computes as many coefficients as required for precision pr
*/
function ComputeZetas(pr)
	vprint Kleinian: "precomputing zeta values";
	zeta := RiemannZeta( : Precision := pr);
	Nzeta := Floor(pr/Log(10,4))+1;
	zetas := [(Evaluate(zeta, 2*n))/(n*(2*n+1)) : n in [1..Nzeta]];
    return zetas;
end function;

function Lobachevsky(x, zetas)
	R := Parent(zetas[1]);
	pr := Precision(zetas[1]);
	pi := Pi(R);

	if x lt 0 then
		return -Lobachevsky(-x, zetas);
	elif x ge pi then
		return Lobachevsky(x-Floor(x/pi)*pi, zetas);
	elif x gt pi/2 then
		return -Lobachevsky(pi-x, zetas);
	elif x eq 0 then
		return 0;
	else
		value := R!0;
		N := Floor(pr/Log(10,4))+1;

		quo := x / pi;
		quo2 := quo^2;
		invquo2 := 1/quo2;
		logquo := Log(10,invquo2);
		N := Floor( (pr + Log(10, 2/3) - Log(10, 1 - quo2))/logquo );

		for n:=N to 1 by -1 do
			value +:= zetas[n];
			value *:= quo2;
		end for;
		value *:= x;
		value +:= x - x*Log(2*x);

		return value;
	end if;
end function;

function StandardParametersVolume(alpha, gamma, zetas)
	R := Parent(zetas[1]);
	hpi := Pi(R)/2;
	return 1/4*(Lobachevsky(alpha+gamma,zetas) + Lobachevsky(alpha-gamma,zetas) + 2*Lobachevsky(hpi-alpha, zetas));
end function;

function StandardTetrahedronVolume(y,z,zetas,eps12) //x=0, y,z in C, OBC = pi/2, sqrnorm(y,z)<=1, tetrahedron based on unit hemisphere with one vertex at infinity.
	dist := Abs(y-z);
	R := Parent(zetas[1]);
	pr := Precision(R);
	if Abs(z) le eps12 or dist le eps12 then return R!0; end if;
	cosalpha := Abs(y)/Abs(z);
	cosgamma := Abs(y);
    if cosalpha ge 1 then
        alpha := 0*eps12;
    else
    	alpha := Arccos(cosalpha);
    end if;
	gamma := Arccos(cosgamma);
	return StandardParametersVolume(alpha, gamma, zetas);
end function;

function NormalizedCenteredTetrahedronVolume(y,z,zetas,eps12) //x=0, y,z in C, sqrnorm(y,z)<=1, tetrahedron based on unit hemisphere with one vertex at infinity.
	N := Norm(z-y);
	R := Parent(zetas[1]);
	pr := Precision(R);
	if N lt eps12 then return R!0; end if;
	t := -Re(y*Conjugate(z-y))/N;
	D := y + t*(z-y);
	return Abs( Sign(Im(D*Conjugate(z)))*StandardTetrahedronVolume(D,z, zetas, eps12) + Sign(Im(y*Conjugate(D)))*StandardTetrahedronVolume(D,y, zetas,eps12) );
end function;

function NormalizedTetrahedronVolume(x,y,z, zetas, eps12) //x,y,z in C, sqrnorm(x,y,z)<=1, tetrahedron based on unit hemisphere with one vertex at infinity.
	return Abs( Sign(Im(y*Conjugate(z)))*NormalizedCenteredTetrahedronVolume(y,z,zetas,eps12) + Sign(Im(x*Conjugate(y)))*NormalizedCenteredTetrahedronVolume(x,y, zetas,eps12) + Sign(Im(z*Conjugate(x)))*NormalizedCenteredTetrahedronVolume(x,z, zetas,eps12) );
end function;

function InfinityVertexTetrahedronVolume(x,y,z, zetas,eps12) //x,y,z in H^3, tetrahedron with one vertex at infinity
	R := Parent(zetas[1]);
	C<I> := ComplexField(R);
	s := PointsToSphere(x,y,z);
	if s`Radius eq 0 then return 0; end if; //un epsilon ?
	X := (x-s`Center)/s`Radius;
	Y := (y-s`Center)/s`Radius;
	Z := (z-s`Center)/s`Radius;
	return NormalizedTetrahedronVolume(C!X[1]+I*X[2], C!Y[1]+I*Y[2], C!Z[1]+I*Z[2], zetas, eps12);
end function;

function SemiIdealTetrahedronVolume(X,Y,Z,v,zetas,eps12) //X,Y,Z in H^3, one vertex v in C (represented in R+Ri subset H)
	R := Parent(zetas[1]);
	if Norm(X-v) le eps12 or Norm(Y-v) le eps12 or Norm(Z-v) le eps12 then
		return R!0;
	end if;
	return InfinityVertexTetrahedronVolume(1/(v-X), 1/(v-Y), 1/(v-Z), zetas, eps12);
end function;

//passer en function ?
intrinsic InfinityEnd(X :: AlgQuatElt, Y :: AlgQuatElt) -> AlgQuatElt, AlgQuatElt //the ends on the sphere at infinity of the geodesic between x and y
{}
	x := X;
	x[3] := 0;
	y := Y;
	y[3] := 0;
	
	alpha := (sqrnorm(X)-sqrnorm(Y) + 2*(sqrnorm(y)-scalar(x,y)))/sqrnorm(x-y);
	beta := (sqrnorm(Y)-sqrnorm(X) + 2*(sqrnorm(x)-scalar(x,y)))/sqrnorm(x-y);
	
	S := alpha*x + beta*y;
	P := scalar(S,(x+y)/2) - (sqrnorm(X)+sqrnorm(Y))/2;
	delta := sqrnorm(S)/4-P;
	r := Sqrt(delta);
	u := (y-x)/Sqrt(sqrnorm(y-x));
	return S/2+r*u, S/2-r*u;
end intrinsic;

function TetrahedronVolume(X,Y,Z,V,zetas,eps12) //x,y,z,v in H^3
	R := Parent(zetas[1]);
	if Norm(X-Y) le eps12 or Norm(X-Z) le eps12 or Norm(X-V) le eps12 or Norm(Y-Z) le eps12 or Norm(Y-V) le eps12 or Norm(Z-V) le eps12 then
		return R!0;
	end if;
	v := InfinityEnd(X,V);
	vol := SemiIdealTetrahedronVolume(X,Y,Z,v,zetas,eps12) - SemiIdealTetrahedronVolume(V,Y,Z,v,zetas,eps12);
    return vol;
end function;

function PolyhedronVolume(F, E, zetas) //F : faces, E : edges.
	H<i,j,k> := Parent(F[1]`Center);
    R := BaseField(H);
    eps12 := epsilon(1/2, Precision(R));
	
	EdgesOfFace := [[] : f in F];
	m := #E;
	for e := 1 to m do
		for f in E[e][3] do
			Append(~EdgesOfFace[f], EndPoints(E[e]));
		end for;
	end for;
	
	TetrahedraVertices := [];
	n := #F;
	for f := 1 to n do
	    if #EdgesOfFace[f] eq 0 then return Infinity(); end if;
		x0 := Rep(EdgesOfFace[f][1]);
		for ep in EdgesOfFace[f] do
			Append(~TetrahedraVertices, [PerturbatedBtoH(j,x0)] cat [PerturbatedBtoH(j,w) : w in ep]);
		end for;
	end for;
      	x00 := Rep(EdgesOfFace[1][1]);
	x00 := PerturbatedBtoH(j,x00);
    vol := R!0;
    for t in TetrahedraVertices do
        volt := TetrahedronVolume(t[1],t[2],t[3],x00,zetas,eps12);
        vol +:= volt;
    end for;
    return vol;
end function;

function PolyhedronArea(F,E)
	R := Parent(F[1]`Radius);
	pi := Pi(R);
    ar := R!0;
    for e in E do
        fe := SetToSequence(e[3]);
        ar -:= IntersectionAngle(F[fe[1]],F[fe[2]]);
    end for;
    ar +:= (#F-2)*pi;
    return ar;
end function;

