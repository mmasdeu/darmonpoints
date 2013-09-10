/*

maple.m
Functions for producing Maple code drawing fundamental domains

maple.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../geometry/intervals.m" : PointInInterval;
import "../geometry/basics.m" : PointInCircle, Sphere, Circle;
import "../kleinian.m" : Hdef, Rdef, Jdef, Idef;

intrinsic MapleReal(a::FldReElt) -> MonStgElt
{Returns 'a' as a string}
	R := RealField(10);
	if a gt 0 then
		return Sprint(R!a);
	else
		return "("*Sprint(R!a)*")";
	end if;
end intrinsic;

intrinsic MapleCoordinates(x::AlgQuatElt) -> MonStgElt
{Returns the coordinates of x as a string}
	Co := Coordinates(x);
	return MapleReal(Co[1]) * "," * MapleReal(Co[2]) * "," * MapleReal(Co[3]);
end intrinsic;

intrinsic MaplePoint(x::AlgQuatElt) -> MonStgElt
{Returns the Maple command to plot x}
	return "point([" * MapleCoordinates(x) * "],symbol=solidsphere,color=blue)";//or cross ?
end intrinsic;

intrinsic MapleCaption(Cap::MonStgElt, x::AlgQuatElt) -> MonStgElt
{Returns the Maple command to plot the string Cap at the position x}
	return "textplot3d([" * MapleCoordinates(x) * ",\"" * Cap * "\"],symbol=solidsphere,color=blue)";
end intrinsic;

intrinsic MapleEdgeCaption(E::Tup, n::RngIntElt) -> MonStgElt
{Returns the Maple command to plot the number n in the middle of the edge E}
	theta := PointInInterval(E[2]);
	x := PointInCircle(E[1], theta);
	return MapleCaption(Sprint(n),x);
end intrinsic;

intrinsic MapleSphere(S::Rec : Transparency := 67 , Grid := false) -> MonStgElt
{Returns the Maple command to plot S}
	if Grid then
		return "sphere([" * MapleCoordinates(S`Center) * "]," * MapleReal(S`Radius) * ",transparency=" * IntegerToString(Transparency) * "*0.01)";
	else
		return "sphere([" * MapleCoordinates(S`Center) * "]," * MapleReal(S`Radius) * ",transparency=" * IntegerToString(Transparency) * "*0.01,style=patchnogrid)";
	end if;
end intrinsic;

intrinsic MapleCircle(C::Rec : Interval := [0.,2*Pi(RealField())], Dash := false, Color := "red") -> SeqEnum[MonStgElt]
{Returns the Maple command to plot C}
	H<i,j,k> := Parent(C`e3);
	x1 := C`e1;
	x2 := C`e2;
	Co := Coordinates(C`Center);
	Rad := MapleReal(C`Radius);
	
	n := #Interval;
	m := n div 2;
	
	if Dash then
		Sdash := ",linestyle=dot";
	else
		Sdash := "";
	end if;
	
	return ["spacecurve([" 
		* MapleReal(Co[1]) * "+" * Rad * "*cos(t)*" * MapleReal(x1[1]) * "+" * Rad * "*sin(t)*" * MapleReal(x2[1]) * "," 
		* MapleReal(Co[2]) * "+" * Rad * "*cos(t)*" * MapleReal(x1[2]) * "+" * Rad * "*sin(t)*" * MapleReal(x2[2]) * ","
		* MapleReal(Co[3]) * "+" * Rad * "*cos(t)*" * MapleReal(x1[3]) * "+" * Rad * "*sin(t)*" * MapleReal(x2[3])
		* "],t=" * MapleReal(Interval[2*i-1]) * ".." * MapleReal(Interval[2*i]) * ",thickness=1,color="* Color * Sdash * ")" : i in [1..m]];
end intrinsic;

intrinsic MapleExteriorDomain(F::SeqEnum, FE::SeqEnum, IE::SeqEnum : Caption := false, Sphere := false) -> SeqEnum[MonStgElt]
{Returns the Maple command to plot the exterior domain with faces F, finite edges FE, infinite edges IE}
	nfe := #FE;
	nie := #IE;
	if Caption then
		S := [MapleEdgeCaption(FE[e],e) : e in [1..nfe]] cat [MapleEdgeCaption(IE[e],e) : e in [1..nie]];
	else
		S := [];
	end if;
	if Sphere then
	  UnitSphere := Sphere(Hdef!0, 1.);
	  sph := [MapleSphere(UnitSphere : Transparency := 100, Grid := true)];
	else
	  sph := &cat[MapleCircle(Circle(Hdef!0,Rdef!1,Hdef!1) : Color := "black"),MapleCircle(Circle(Hdef!0,Rdef!1,Idef) : Color := "black"),MapleCircle(Circle(Hdef!0,Rdef!1,Jdef) : Color := "black"), ["spacecurve([t,0,0], t=-1..1, thickness=1,color=black)","spacecurve([0,t,0], t=-1..1, thickness=1,color=black)","spacecurve([0,0,t], t=-1..1, thickness=1,color=black)"]];
	end if;
	
	return sph
		cat [MapleSphere(s : Transparency := 85) : s in F] 
		cat (&cat[MapleCircle(e[1] : Interval := e[2]) : e in FE cat IE])
		cat S;
end intrinsic;

intrinsic MapleDraw(s::SeqEnum[MonStgElt] : view := 0) -> MonStgElt
{Returns the Maple command to display the plots defined by the commands of the sequence s}
	Str := "with(plottools): with(plots): s:=";
	tail := "";
	if not IsEmpty(s) then
		tail := Reverse(s)[1];
		prune := Prune(s);
		for x in prune do
			Str := Str * x * ",";
		end for;
	end if;
	if view eq 0 then
		V := "";
	else
		a := MapleReal(view);
		V := ",view=[-" * a * ".." * a * "," * "-" * a * ".." * a * "," * "-" * a * ".." * a * "]";
	end if;
	return Str * tail * ": display(s,scaling=constrained" * V * ");";
end intrinsic;

intrinsic MapleFile(s::MonStgElt, file::MonStgElt)
{Create a Maple input file "file.mpl" which contains the commands s}
	F := Open(file*".mpl", "w");
	Put(F,s);
	Flush(F);
end intrinsic;

