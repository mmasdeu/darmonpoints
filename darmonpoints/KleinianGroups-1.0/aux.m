/*

aux.m
Auxiliary and printing functions

aux.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/

function epsilon(r,Precision)
	R := RealField(Precision);
	return 10^(-R!(r*Precision));
end function;

procedure PrintCircle(C,pr)
	R := RealField(pr);
	print "center", R!(C`Center)[1], R!(C`Center)[2],R!(C`Center)[3], " - radius", R!(C`Radius), " - ortho", R!(C`e3)[1], R!(C`e3)[2],R!(C`e3)[3];
end procedure;

procedure PrintSphere(S,pr)
	R := RealField(pr);
	print "center", R!(S`Center)[1], R!(S`Center)[2],R!(S`Center)[3], " - radius", R!(S`Radius);
end procedure;

procedure PrintInterv(I,pr)
	R := RealField(pr);
	print [R!I[i] : i in [1..#I]];
end procedure;

procedure PrintSizeExtDom(F,FE,IE)
	vprint Kleinian, 2: "#F",#F,"#FE",#FE,"#IE",#IE;
end procedure;
