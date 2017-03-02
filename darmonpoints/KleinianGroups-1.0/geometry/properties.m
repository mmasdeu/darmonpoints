/*

properties.m
procedures for computing geometric properties of a Kleinian group

properties.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../kleinian.m" : isscalar, kleinianmatrix, displacement;
import "basics.m" : Distance, EndPoints, action;
import "../aux.m" : epsilon;

function polyrad(edges) //assumes that the polyhedron is bounded.
    zero := Parent(edges[1][1]`Center)!0;
    rad := Max([Max([Distance(zero,x) : x in EndPoints(e)]) : e in edges]);
    return rad;
end function;

intrinsic Radius(Edges :: SeqEnum) -> FldReElt
{
    The radius of the smallest hyperbolic ball centered at 0 containing the compact polyhedron with sequence of edges Edges.
}
    return polyrad(Edges);
end intrinsic;

procedure elimdup(~L, i, eps)
    isunique := true;
    for step in {-1,1} do
        j := i+step;
        while isunique and j ge 1 and j le #L and Abs(L[j][1]-L[i][1]) le eps do
            if isscalar(L[j][2]/L[i][2]) then
                isunique := false;
            end if;
            j +:= step;
        end while;
    end for;
    if not isunique then
        Remove(~L, i);
    end if;
end procedure;

procedure dichoinsert(~L, x, eps)
    a := 0;
    b := #L+1;
    while b-a gt 1 do
        c := (a+b) div 2;
        if x[1] lt L[c][1] then
            b := c;
        else
            a := c;
        end if;
    end while;
    Insert(~L, b, x);
    elimdup(~L, b, eps);
end procedure;

intrinsic Systole(faces :: SeqEnum, edges :: SeqEnum) -> FldReElt
{
    The minimum displacement of a loxodromic element in a Kleinian group, given the faces and edges of its Dirichlet domain.
}
    pr := Precision(faces[1]`Center[3]);
    eps := epsilon(1/10, pr);
    zero := Parent(edges[1][1]`Center)!0;
    rad := polyrad(edges) + eps;
    muls := [f`g : f in faces];
    L := [<Distance(zero, action(f`Matrix, zero)), f`g> : f in faces];
    Sort(~L);
    systol := -1;

    //hope the systole is among those
    for x in L do
        lg := x[1];
        g := x[2];
        depl := displacement(g,pr);
        if depl gt eps and (systol eq -1 or depl lt systol) then
            systol := depl;
        end if;
    end for;

    while systol eq -1 or #L ne 0 do

        vprint Kleinian, 3 : "#L", #L, "\tsystole", RealField(6)!systol;

        lg := L[1][1];
        g := L[1][2];
        Remove(~L, 1);

        depl := displacement(g,pr);
        if depl gt eps and (systol eq -1 or depl lt systol) then
            systol := depl;
        end if;

        for m in muls do
            mg := m*g;
            lmg := Distance(zero, action(kleinianmatrix(mg),zero));
            if lmg gt lg and (systol eq -1 or lmg le 2*rad+systol) then
                dichoinsert(~L, <lmg,mg>, eps);
            end if;
        end for;
    end while;
    return systol;
end intrinsic;

