/*

basics.m
Basic geometric functions

basics.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../aux.m" : epsilon;
import "../kleinian.m" : kleinianmatrix, isscalar;

function vecprod(x,y)
	H := Parent(x);
	return H![x[2]*y[3]-x[3]*y[2] , x[3]*y[1]-x[1]*y[3] , x[1]*y[2]-x[2]*y[1] , 0];
end function;

function colinear(x,y,eps12)
	return Abs(x[2]*y[3]-x[3]*y[2]) le eps12 and Abs(x[3]*y[1]-x[1]*y[3]) le eps12 and Abs(x[1]*y[2]-x[2]*y[1]) le eps12;
end function;

function m(x, y, z)
	return (x[2]*y[3]-x[3]*y[2])*z[1] + (x[3]*y[1]-x[1]*y[3])*z[2] + (x[1]*y[2]-x[2]*y[1])*z[3];
end function;

function scalar(x,y)
	return x[1]*y[1]+x[2]*y[2]+x[3]*y[3];
end function;

function sqrnorm(x)
	return x[1]^2+x[2]^2+x[3]^2+x[4]^2;
end function;

Sphr := recformat<Center : AlgQuatElt , Radius : FldReElt, g : AlgQuatElt, Matrix : AlgMatElt, Edges : SetEnum >;

function Sphere(center, radius)
	error if radius lt 0, "the radius must be positive."; 
	return rec<Sphr | Center := center, Radius := radius>;
end function;

function PlaneBasis(N)
	H<i,j,k> := Parent(N);
	e1 := i*N;
	e1[4] := 0;
	if e1 eq 0 then
		e1+:=H!1;
	else
		e1 := e1/Sqrt(sqrnorm(e1));
	end if;
	e2 := vecprod(N,e1);
	e2 := e2/Sqrt(sqrnorm(e2));
	return e1,e2;
end function;

Crcl := recformat<Center : AlgQuatElt , Radius : FldReElt , e1 : AlgQuatElt, e2 : AlgQuatElt, e3 : AlgQuatElt>;

function Circle(center, radius, orthogonal)
	error if radius lt 0, "the radius must be positive.";
	error if orthogonal eq 0, "the orhogonal vector must be nonzero.";
	e1,e2 := PlaneBasis(orthogonal);
	return rec<Crcl | Center := center , Radius := radius , e1 := e1, e2 := e2, e3 := orthogonal>;
end function;

function AngleInPlane(x, e1, e2)//e1,e2 orthonormal
	R := BaseField(Parent(x));
	C<I> := ComplexField(R);
	z := scalar(x,e1)+I*scalar(x,e2);
	error if z eq 0, "The angle is not defined when x is orthogonal to <e1,e2>.";
	theta := Arg(z);
	if theta lt 0 then theta := theta + 2*Pi(R); end if;
	return theta;
end function;

function PointInCircle(C, theta)
	return C`Center+C`Radius*(Cos(theta)*C`e1+Sin(theta)*C`e2);
end function;

function Delta(u,v)
	return sqrnorm(u-v)/((1-sqrnorm(u))*(1-sqrnorm(v)));
end function;

function Distance(u, v)
	return Argcosh(1+2*Delta(u,v));
end function;

function action(g, w)
	HH := Parent(w);
	pr := Precision(BaseField(HH));
	gw := (g[1,1]*w+g[1,2])/(g[2,1]*w+g[2,2]);
	gw[4] := 0;
	if sqrnorm(gw) ge 1 then
		gw := gw/Sqrt(sqrnorm(gw));
		gw *:= HH!(1 - epsilon(9/10,pr));
	end if;
	return gw;
end function;

intrinsic '*'(g::AlgMatElt, w::AlgQuatElt) -> AlgQuatElt
{
    Action of g on the point w in the unit ball model of the hyperbolic 3-space
}
    return action(g, w);
end intrinsic;

function MatrixIsometricSphere(m)
	error if sqrnorm(m[2,1]) le 0, "This element has no isometric sphere.", m, Norm(m[2,1]), sqrnorm(m[2,1]);
	center := -(1/m[2,1]) * m[2,2];
	center[4] := 0;
	
	return rec<Sphr | Center := center, Radius := 1/Sqrt(sqrnorm(m[2,1])), Matrix := m>;
end function;

function IsometricSphere(g, eps)
	S := MatrixIsometricSphere(kleinianmatrix(g));
	S`g := g;
	return S;
end function;

function ZerotoP(p, MR)
	H := BaseRing(MR);
    if p eq 0 then
        r2 := 1;
    else
        r2 := 1-sqrnorm(p);
    end if;
    if r2 le 0 then
        vprint Kleinian : "WARNING, correction of p";
        return ZerotoP((1-epsilon(9/10,pr))*p, MR) where pr := Precision(BaseField(H));
    end if;
	ri := 1/Sqrt(r2);
	return ri*(MR![1,-p,Conjugate(p),-1]), ri*(MR![-1,p,-Conjugate(p),1]);
end function;

function JtoP(p, MR)
	C<I>:= BaseRing(MR);
	a := p[1]+I*p[2];
	t := p[3];
	error if t le 0, "p is not an element of H3.";
	st := Sqrt(t);
	return MR![st,a/st,0,1/st], MR![1/st,-a/st,0,st];
end function;

function IsInterior(w, S, eps12)
	return sqrnorm(w-S`Center) le (S`Radius)^2*(1+eps12);
end function;

function IsExterior(w, S, eps12)
	return sqrnorm(w-S`Center) ge (S`Radius)^2*(1-eps12);
end function;

function IntersectionAngle(S1,S2)
	cosa := (sqrnorm(S1`Center-S2`Center)-((S1`Radius)^2+(S2`Radius)^2)) / (2*S1`Radius*S2`Radius);
	error if Abs(cosa) gt 1, "The spheres do not intersect.";
	return Arccos(cosa);
end function;

function SpheresIntersection(S1, S2, eps12)
	N := S2`Center - S1`Center;
	D := sqrnorm(N);
	if D le eps12 then
		return rec<Crcl | Radius := -1. >; //Radius = -1 : empty set.  Warning, incorrect result if spheres are the same.
	end if;
	
	M := (S2`Center + S1`Center)/2;
	R1 := S1`Radius;
	R2 := S2`Radius;
	Rsqr := ((R1+R2)^2-D)*(D-(R1-R2)^2)/(4*D);
	if Rsqr lt 0 or (Rsqr lt eps12 and Trace(S1`g)^2 eq 4 and Trace(S2`g)^2 eq 4 and isscalar(S1`g*S2`g/(S2`g*S1`g))) then
		return rec<Crcl | Radius := -1. >;
	else
		return Circle(M+(R1^2-R2^2)/(2*D)*N, Sqrt(Rsqr), N);
	end if;
end function;

function PlanesIntersection(X1, N1, X2, N2)
	Y := vecprod(N1,N2);
	Z := vecprod(Y,N2);
	a := m(Y,N2,N1);
	b := scalar(N1,X1-X2);
	error if a eq 0, "The planes are parallel.";
	return X2+b/a*Z,Y; //point, direction.
end function;

function PointsToSphere(x,y,z)
	H := Parent(x);
	a := (y-x)[1];
	b := (y-x)[2];
	c := (z-x)[1];
	d := (z-x)[2];
	alpha := (sqrnorm(y)-sqrnorm(x))/2;
	beta := (sqrnorm(z)-sqrnorm(x))/2;
	D := a*d-b*c;
	if D eq 0 then return Sphere(x,BaseField(H)!0); end if;
	t1 := (d*alpha - b*beta)/D;
	t2 := (a*beta - c*alpha)/D;
	Y := H!t1 + t2*H.1;
	return Sphere(Y, Sqrt(sqrnorm(Y-x)));
end function;

function EndPoints(e)
	Interv := e[2];
	return {PointInCircle(e[1],Interv[2]), PointInCircle(e[1],Interv[1+(2 mod #Interv)])};
end function;

function BtoH(j,w)
	return (1/(1+w*j)) * (w+j);
end function;

function PerturbatedBtoH(j,w)
	if w eq j then
		return Parent(j)!(1000000000/1174263548);
	else
		z := BtoH(j,w);
		return z/(1174263548/1000000000*z+1);
	end if;
end function;

function SameSphere(S1, S2, eps)
	b := sqrnorm(S1`Center-S2`Center) lt eps^2
		and Abs(S1`Radius-S2`Radius) lt eps;
	return b;
end function;

function SameCircle(C1, C2, eps)
	b := sqrnorm(C1`Center-C2`Center) lt eps^2
		and Abs(C1`Radius-C2`Radius) lt eps
		and sqrnorm(vecprod((C1`e3),(C2`e3)))*C1`Radius*C2`Radius lt sqrnorm(C1`e3)*sqrnorm(C2`e3)*eps^2;//affaiblir cette condition en enlevant les rayons ?
	return b;
end function;
