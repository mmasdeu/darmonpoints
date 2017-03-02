/*

intervals.m
basic functions for handling finite unions of intervals

intervals.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/

/*
    INPUT
    L : a sequence representing intervals
    treshold : an integer

    OUTPUT
    a sequence representing a disjoint union of intervals, the set of points x such that there are at least treshold intervals from L covering x
*/
function MergeIntervals(L, treshold)//treshold = 1 -> union, treshold = #L/2 -> intersection
	error if #L mod 2 ne 0, "#L must be even.";
	n := #L div 2;
	L2 := [<L[2*i-1],1> : i in [1..n]] cat [<L[2*i],-1> : i in [1..n]];
	Sort(~L2);
	L3 := [];
	count := 0;
	flag := false;
	N := 2*n;
	for i := 1 to N do
		count +:= L2[i][2];
		if count ge treshold xor flag then
			flag := not flag;
			Append(~L3,L2[i][1]);
		end if;
	end for;
	return L3;
end function;

function UnionIntervals(L)
	return MergeIntervals(L,1);
end function;

function IntersectionIntervals(L)
	return MergeIntervals(L,#L div 2);
end function;

function IntersectionCompacts(Li, B) //The compacts must be in normal form. If not, apply UnionIntervals.
	k := #Li;
	if k ne 0 then
		return MergeIntervals(&cat Li, k); //does not control whether every given interval is inside [0,B].
	else //an empty intersection returns the full interval [0,B];
		return [0*B,B];
	end if;
end function;

procedure ComplementInterval(~L, B) //complement in [0,B]
	n := #L;
	R := Parent(B);
	if n eq 0 then
		L := [R!0,B];
	else
		if L[n] eq B then
			Prune(~L);
		else
			Append(~L,B);
		end if;
		if L[1] eq R!0 then
			Exclude(~L,R!0);
		else
			Insert(~L,1,R!0);
		end if;
	end if;
end procedure;

function LengthInterval(L)
	n := #L div 2;
	if n eq 0 then
		return 0;
	else
        s := Parent(L[1])!0;
        maxi := 2*n;
        for i := 1 to maxi by 2 do
            s +:= L[i+1]-L[i];
        end for;
        return s;
	end if;
end function;

function PointInInterval(L)
	R := Parent(L[1]);
	pi2 := 2*Pi(R);
	n := #L;
	if L[1] eq 0 and L[n] eq pi2 then
		theta := (L[n-1]+L[2]+pi2)/2;
		if theta ge pi2 then
			theta -:= pi2;
		end if;
		return theta;
	else
		return (L[1]+L[2])/2;
	end if;
end function;

function IsInInterval(L, x)
	n := #L;
	error if n mod 2 ne 0, "#L must be even";
	
	if x lt L[1] then return false; end if;
	if x ge L[n-1] then return x le L[n]; end if;
	
	i := 1;
	j := n div 2;
	while i+1 lt j do
		k := (i+j) div 2;
		if x lt L[2*k-1] then
			j := k;
		else // x ge L[2*k-1]
			i := k;
		end if;
	end while;
	return x le L[2*i];
end function;
