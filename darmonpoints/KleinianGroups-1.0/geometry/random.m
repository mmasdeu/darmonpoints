/*

random.m
functions for generating various random objects

random.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../aux.m" : Hdef;
import "volumes.m" : VolumeDisc, VolumeBall, dVolumeBall;
import "basics.m" : PointInCircle;
import "intervals.m" : LengthInterval;

function RandomReal(r)
 R := Parent(r);
 pr := Precision(R);
 return R!(Random(Floor(r*10^pr))*10^(-pr));
end function;

function RandomInInterval(I)
len := LengthInterval(I);
x := RandomReal(len);
k := 1;
ni := #I;
while 2*k+1 le ni and x+I[2*k-1] gt I[2*k] do
    x -:= I[2*k]-I[2*k-1];
    k +:= 1;
end while;
return x+I[2*k-1];
end function;

function RandomInCircle2(R)
 repeat
  x := 2*RandomReal(R!1)-1;
  y := 2*RandomReal(R!1)-1;
  w := x^2 + y^2;
 until w le 1;
 w := Sqrt(w);
 return [x/w,y/w];
end function;

function RandomInSphere(R)
 repeat
  x := 2*RandomReal(R!1)-1;
  y := 2*RandomReal(R!1)-1;
  z := 2*RandomReal(R!1)-1;
  w := x^2 + y^2 + z^2;
 until w le 1;
 w := Sqrt(w);
 return [x/w,y/w,z/w];
end function;

/*
    The (hyperbolic) radius of the (hyperbolic) disc of (hyperbolic) area v
*/
function RadiusDisc(v)
 R := Parent(v);
 return Argcosh(1+v/(2*Pi(R)));
end function;

/*
    An approximation of the (hyperbolic) radius of the (hyperbolic) ball of (hyperbolic) volume v 
*/
function ApproxRadiusBall(v)
 R := Parent(v);
 return Max(Log(2*v/Pi(R))/2,R!1/10);
end function;

/*
    The (hyperbolic) radius of the (hyperbolic) ball of (hyperbolic) volume v 
*/
function RadiusBall(v,eps)
 veps := v*eps;
 if v le eps then
  return (3*v/(4*Pi(Parent(v))))^(1/3);
 end if;
 r := ApproxRadiusBall(v);
 repeat
  diffe := VolumeBall(r)-v;
  r := r - diffe/dVolumeBall(r);
 until Abs(diffe) lt veps;
 return r;
end function;

/*
    Returns a random point in the (hyperbolic) disc of radius r, with distribution law given by the hyperbolic area
*/
function RandomHyperbolicDisc(H,r)
 R := BaseField(H);
 v := RandomReal(VolumeDisc(R!r));
 w := RandomInCircle2(R);
 rh := RadiusDisc(v);
 chrh := Cosh(rh);
 re := Sqrt((chrh-1)/(chrh+1));
return re*(w[1]*H.2+w[2]*H![1,0,0,0]);
end function;

/*
    Returns a random point in the (hyperbolic) ball of radius r, with distribution law given by the hyperbolic volume
*/
function RandomHyperbolicBall(H,r,eps)
 R := BaseField(H);
 v := RandomReal(VolumeBall(R!r));
 w := RandomInSphere(R);
 rh := RadiusBall(v,eps);
 chrh := Cosh(rh);
 re := Sqrt((chrh-1)/(chrh+1));
return re*(w[1]*H.1+w[2]*H.2+w[3]*H![1,0,0,0]);
end function;

function RandomQuatIJ( : H := Hdef)
	_,i,j := Explode(Basis(H));
	return Random((200)-100)/100 +  (Random(200)-100)/100*i + (Random(200)-100)/100*j;
end function;

//un peu obsolete avec RandomHyperbolicBall, mais pas la même loi...
function RandomInUnitBall( : H := Hdef)
	_,i,j := Explode(Basis(H));
	z := Random(10000) + Random(10000)*i + Random(10000)*j;
	n := 1 - 50/(50+Random(10000));
	z := z*n/Sqrt(Norm(z));
	return z;
end function;

function RandomInCircle(C)
	theta := Random(10000);
	return PointInCircle(C, theta);
end function;

function randprod(L)
    rid := Random(L);
    while Random(5) eq 0 do
        rid *:= Random(L);
    end while;
    return rid;
end function;

