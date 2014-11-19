/*

exteriordomains.m
procedures for computing the exterior domain of a finite subset of a Kleinian group

exteriordomains.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../kleinian.m" : DefaultPrecision;
import "basics.m" : IsExterior, SphereCircleIntersection, AngleInPlane, IsInterior, PointInCircle, Sphere, SpheresIntersection, SameCircle, SameSphere, sqrnorm, colinear, vecprod, scalar, m;
import "random.m" : RandomInCircle;
import "intervals.m" : PointInInterval, IntersectionCompacts, LengthInterval;
import "../aux.m" : epsilon;
import "../fundamentaldomains/normalizedbasis.m" : CheckTimeOut;

function IsInExteriorDomain(w,L,eps)
	for s in L do
		//if not IsExterior(w,s,eps12) then : inline
        if sqrnorm(w-s`Center) lt (s`Radius)^2*(1-eps) then
			return false;
		end if;
	end for;
	return true;
end function;

/*
    INPUT
    C : a circle
    S : a sphere
    interior : a boolean
    eps12 : a small real for handling approximation, 10^(-pr/2)

    OUTPUT
    The union of intervals in [0,2*Pi] corresponding to the points of C that are in the interior/exterior of S, according to 'interior'.
*/
function CutInterval(C, S, interior, eps12)
    CCenter := C`Center;
    Ce1 := C`e1;
    Ce2 := C`e2;
    Ce3 := C`e3;
    SCenter := S`Center;
	R1 := S`Radius;
	R2 := C`Radius;
	H := Parent(Ce3);
	R := BaseField(H);
	pi2 := 2*Pi(R);
	
	if R2 ge eps12 then //Avant : eps(6/10)
        
   //function SphereCircleIntersection(S, C, eps12) : inline
	N := CCenter - SCenter;
	D := sqrnorm(N);
	
    if D ge (R1+R2)^2 then
        if interior then
            return [];
        else
            return [R!0,pi2];
        end if;
    else 
        //à remplacer par des epsilons ?
        if R2 eq 0 then
            if D eq R1^2 then
                Inter := [CCenter];
            else
                Inter := [];
            end if;
        else
            
            if D le eps12 then //Avant : eps(1/3)
                if Abs(R1-R2) le eps12 then
                    p0 := PointInCircle(C,0);
                    Inter := [p0,p0,p0];
                else
                    Inter := []; //Warning : incorrect if the circle is a geodesic on the sphere
                end if;
            else
                
                M := (CCenter + SCenter)/2;
                Cent := M+(R1^2-R2^2)/(2*D)*N;
                
                if not colinear(N,Ce3,eps12) then

                    //Pt,Y := PlanesIntersection(C`Center,C`e3,Cent,N);
                    //function PlanesIntersection(X1, N1, X2, N2) : inline
                    Y := vecprod(Ce3,N);
                    a := m(Y,N,Ce3);
                    Z := vecprod(Y,N);
                    b := scalar(Ce3,CCenter-Cent);
                    Pt := Cent+b/a*Z;
                    //end function;
                    
                    A := sqrnorm(Y);
                    B := scalar(Y,Pt-SCenter);
                    CC := sqrnorm(Pt-SCenter)-R1^2;
                    
                    Delta := B^2-4*A*CC;
                    if Delta lt 0 then
                        Inter := [];
                    elif Delta/A gt eps12*R2 then //Avant : eps(2/3)
                        SD := Sqrt(Delta);
                        Inter := [Pt+((-B+SD)/(2*A))*Y,Pt-((B+SD)/(2*A))*Y];
                    else //Delta eq 0
                        vprint Kleinian, 1: "Warning : unique intersection";
                        ptinter := Pt-B/(2*A)*Y;
                        Inter := [ptinter];
                    end if;
                
                else //plans paralleles
                    if Abs(R1^2-R2^2-D) le eps12 then
                        p0 := PointInCircle(C,0);
                        Inter := [p0,p0,p0];
                    else
                        Inter := []; //faux si le cercle est entièrement inclus dans la sphere.
                    end if;
                end if;
            end if;
        end if;
    end if;
        //end function;
        //end inline
        
		//Inter := SphereCircleIntersection(S, C, eps12);
		AnglesInter := [AngleInPlane(x-CCenter, Ce1, Ce2) : x in Inter];
	else
		AnglesInter := [];
	end if;
	
	n := #AnglesInter;
	if n gt 2 then
		return [R!0,pi2];
	elif n le 1 then //dépend si à l'intérieur ou à l'extérieur : tester un point du cercle.
        //ptci := RandomInCircle(C);
        ptci := CCenter + R2*(3/5*Ce1 + 4/5*Ce2);

		if interior then
			correctpt := IsInterior(ptci, S, eps12);
		else
			correctpt := IsExterior(ptci, S, eps12);
		end if;
		if correctpt then
			return [R!0, pi2];
		else
			return [];
		end if;
		
	else //n=2
	
        //sort AnglesInter
        a1 := AnglesInter[1];
        a2 := AnglesInter[2];
        if a1 ge a2 then
            AnglesInter[1] := a2;
            AnglesInter[2] := a1;
        end if;

		theta := PointInInterval(AnglesInter);
		if interior then
			correctpt := IsInterior(PointInCircle(C, theta), S, eps12);
		else
			correctpt := IsExterior(PointInCircle(C, theta), S, eps12);
		end if;
		if correctpt then
			return [AnglesInter[1], AnglesInter[2]];
		else
			return [R!0, AnglesInter[1], AnglesInter[2], pi2];
		end if;
	end if;
end function;

function InteriorInterval(C, S, eps12)
	return CutInterval(C, S, true, eps12);
end function;

function ExteriorInterval(C, S, eps12)
	return CutInterval(C, S, false, eps12);
end function;

/*
    INPUT
    C : a circle
    L : a sequence of spheres
    USPhere : a boolean
    SetL : a set of indices indicationg the spheres in L to be ignored
    eps12 : a small real for handling approximation, 10^(-pr/2)

    OUTPUT
    The union of intervals in [0,2*Pi] corresponding to the set of points that are in the exterior of the spheres in L, and if USphere is set to true, that are also in the interior of the unit sphere.
*/
function IntervalOfCircle(C, L, USphere, SetL, eps12)
	H := Parent(C`e3);
	R := BaseField(H);
	pi2 := 2*Pi(R);
	
	Linterv := [];
	
	//inside the unit sphere
	if USphere then
		UnitSphere := Sphere(H!0,R!1);
		//Interv := InteriorInterval(C, UnitSphere, eps12);
		Interv := CutInterval(C, UnitSphere, true, eps12);
		Append(~Linterv, Interv);
	end if;
	
	//outside the spheres
	n := #L;
	for s := 1 to n do
		if not (s in SetL) then
			//Interv := ExteriorInterval(C, L[s], eps12);
            Interv := CutInterval(C, L[s], false, eps12);
			Append(~Linterv, Interv);
            if s mod 20 eq 19 then
                LInterv := [IntersectionCompacts(Linterv,pi2)];
                if LInterv eq [[]] then
                    return [];
                end if;
            end if;
		end if;
	end for;
	
	Lfin := IntersectionCompacts(Linterv,pi2);
	return Lfin;
end function;

function PointNextToInfinity(S,z,eps)
	z1 := (1-eps)*z;
	z1 := S`Center + (z1-S`Center)*S`Radius/Sqrt(sqrnorm(z1-S`Center));
	return z1;
end function;

/*
    INPUT
    F : a reference to the set of faces of the polyhedron
    E : a reference to a set of edges of the poyhedron
    S : a sphere
    FP : a reference for storing the faces affected by the operation
    start : the index of an edge going to be affected (optional, 0=none, currently unused)
    nbdel : a reference for storing the number of deleted edges before 'start' (used only with 'start')
    eps12 : a small real for handling approximation, 10^(-pr/2)
    eps13 : a small real for handling approximation, 10^(-pr/3)

    Modifies the previously existing edges of the polyhedron, according to cutting it with the half-space exterior to the sphere S
*/
procedure EatEdges(~F, ~E, S, ~FP, start, ~nbdel, eps12, eps13)
	pi2 := 2*Pi(Parent(eps12));
	n := #E;
	ToRemove := [];
    dfs := start ne {};
    if dfs then
        tovisit := start;
        visited := {};
    end if;
    e := 0;
	while (dfs and not IsEmpty(tovisit)) or (not dfs and e lt n) do
					       //CheckTimeOut();
        if dfs then
            ExtractRep(~tovisit, ~e);
            Include(~visited, e);
        else
            e +:= 1;
        end if;
		//Interv := ExteriorInterval(E[e][1],S, eps12);
		Interv := CutInterval(E[e][1],S,false,eps12);
        lg := LengthInterval(E[e][2]);
		E[e][2] := IntersectionCompacts([E[e][2],Interv],pi2);
        if LengthInterval(E[e][2]) lt lg then
            FP join:= E[e][3];
            if dfs then
                for f in E[e][3] do
                    tovisit join:= F[f]`Edges diff visited;
                end for;
            end if;
        end if;
		if LengthInterval(E[e][2]) le eps13 then
			Append(~ToRemove, e);
		end if;
	end while;
    if dfs then
        Sort(~ToRemove);
    end if;
	ntr := #ToRemove;
    limit := nbdel;
    nbdel := 0;
	for i := 1 to ntr do
		Remove(~E, ToRemove[i]-i+1); //shift because of previous suppressions.
        if ToRemove[i] le limit then
            nbdel +:= 1;
        end if;
	end for;
end procedure;

/*
    INPUT
    F : faces of the polyhedron
    S : a sphere
    FP : indices of relevant faces
    eps12 : a small real for handling approximation, 10^(-pr/2)

    OUTPUT
    The new finite edges and the new infinite edges created when cutting the polyhedron with S
*/
function NewEdges(F, S, FP, eps12, eps13)
	H := Parent(S`Center);
	R := BaseField(H);
	UnitSphere := Sphere(H!0,R!1);
	
	NFE := [];
	n := #F;
	for f in FP do
		C := SpheresIntersection(F[f],S,eps12);
		if C`Radius ge eps13 then //Avant : eps(1/3)
			Interv := IntervalOfCircle(C, F, true, {f}, eps12);
			if LengthInterval(Interv) ge eps13 then //Avant : eps(1/3)
				Append(~NFE, <C,Interv,{f,n+1}>);
			end if;
		end if;
	end for;
	
	C := SpheresIntersection(UnitSphere,S,eps12);
	if C`Radius ge eps13 then
		Interv := IntervalOfCircle(C, F, false, {}, eps12);
		if LengthInterval(Interv) ge eps13 then //Avant : eps(1/3)
			NIE := [<C,Interv,{n+1}>];
		else
			NIE := [];
		end if;
	else //should never happen
		NIE := [];
	end if;
	
	return NFE,NIE;
end function;

/*
    INPUT
    F : a reference to the faces of the polyhedron
    E : a reference to the edges of the polyhedron
    NE : the new egdes of the polyhedron
    nbF : the number of faces of the polyhedron
    eps12 : a small real for handling the approximation, 10^(-pr/2)
    eps110 : a small real for handling the approximation, 10^(-pr/10)

    Removes the redundancy in the edges of the polyhedron.
*/
procedure EliminateMultipleEdges(~F, ~E, NE, nbF, eps12, eps110)
	R := Parent(eps12);
	n := #E;
	nn := #NE;
	for nedge := 1 to nn do
		old := false;
		for edge := 1 to n do
			if SameCircle(NE[nedge][1],E[edge][1],eps12) then
				//que faire avec l'intervalle ? Prendre la réunion ? L'intersection ? Ne garder que le "vieux" (actuellement) ?
				E[edge][3] := E[edge][3] join NE[nedge][3];
				old := true;
				break;
			end if;
		end for;
		if not old then
			Append(~E, NE[nedge]);
		end if;
	end for;
	
	n := #E;
	for edge := 1 to n do
        nbFe := #E[edge][3];
		if nbFe gt nbF then
			candidates := [];
            candidatesL := [];
			theta := PointInInterval(E[edge][2]);
			x := PointInCircle(E[edge][1], theta);
			STest := Sphere(x,eps110);
			for f in E[edge][3] do
				CTest := SpheresIntersection(F[f],STest,eps12);
				IntervTest := IntervalOfCircle(CTest, F, true, {f}, eps12);
				LTest := LengthInterval(IntervTest);
                Append(~candidates, f);
                Append(~candidatesL, R!LTest);
			end for;
			//Sort(~candidates, func<x,y | y[2]-x[2]>); //decreasing order wrt the second variable.
			//E[edge][3] := {c[1] : c in candidates[1..nbF]}; 
            if nbF eq 1 then 
                _,imax := Max(candidatesL); 
                E[edge][3] := {candidates[imax]}; 
            else //nbF = 2 

                //max and second
                if candidatesL[1] gt candidatesL[2] then
                    imax1 := 1;
                    imax2 := 2;
                else
                    imax1 := 2; 
                    imax2 := 1; 
                end if; 
                max1 := candidatesL[imax1]; 
                max2 := candidatesL[imax2]; 
                for i := 3 to nbFe do 
                    lgth := candidatesL[i]; 
                    if lgth gt max1 then 
                        imax2 := imax1; 
                        max2 := max1; 
                        imax1 := i; 
                        max1 := lgth; 
                    elif lgth gt max2 then 
                        imax2 := i; 
                        max2 := lgth; 
                    end if; 
                end for;

                E[edge][3] := {candidates[imax1],candidates[imax2]}; 
            end if; 
        end if; 
    end for; 
end procedure; 

/*
    INPUT
    F : a reference to the faces of the polyhedron
    FE : a reference to the finite edges of the polyhedron
    FE : a reference to the intinite edges of the polyhedron

    Removes the redundancy in the faces of the polyhedron.
*/
procedure EliminateFaces(~F, ~FE, ~IE) 
    setF := (&join[ e[3] : e in FE]) join (&join[ e[3] : e in IE]); 
    newF := SetToSequence(setF); 
    n := #newF; 
    indexF := [0 : f in F]; 
    for f := 1 to n do 
        indexF[newF[f]] := f; 
    end for; 
    F := [F[newF[f]] : f in [1..n]]; 
    for f := 1 to n do
        F[f]`Edges := {};
    end for;
    nfe := #FE; 
    for e := 1 to nfe do 
        FE[e][3] := {indexF[f] : f in FE[e][3]}; 
        for f in FE[e][3] do
            Include(~(F[f]`Edges), e);
        end for;
    end for; 
    nie := #IE; 
    for e := 1 to nie do 
        IE[e][3] := {indexF[f] : f in IE[e][3]}; 
    end for; 
end procedure; 

/*
    INPUT
    F : a reference to the faces of the polyhedron
    FE : a reference to the finite edges of the polyhedron
    FE : a reference to the intinite edges of the polyhedron
    S : a sphere
    start : the index of an edge going to be affected (optional, 0=none, currently unused)
    nbdel : a reference for storing the number of deleted edges before 'start' (used only with 'start')
    eps12 : a small real for handling approximation, 10^(-pr/2)
    eps13 : a small real for handling approximation, 10^(-pr/3)
    eps110 : a small real for handling approximation, 10^(-pr/10)

    Modifies the polyhedron, according to intersecting it with the exterior of the sphere S
*/
procedure UpdateExteriorDomain(~F, ~FE, ~IE, S, start, ~nbdel, eps12, eps13, eps110) 
    for f in F do 
        if SameSphere(f,S,eps12) then 
            nbdel := 0;
            return; 
        end if; 
    end for; 
    
    FP := {}; 
    nbdel0 := 0;
    EatEdges(~F, ~IE, S, ~FP, {}    , ~nbdel0, eps12, eps13); 
    if start ne 0 then
        EP := &join[F[f]`Edges : f in FP];
        sstart := Include(EP,start);
    else
        sstart := {};
    end if;
    EatEdges(~F, ~FE, S, ~FP, sstart, ~nbdel , eps12, eps13); 
    NFE, NIE := NewEdges(F, S, FP, eps12, eps13); 
    
    Append(~F,S); 
	
    EliminateMultipleEdges(~F, ~FE, NFE, 2, eps12, eps110);
	EliminateMultipleEdges(~F, ~IE, NIE, 1, eps12, eps110);
	
	EliminateFaces(~F, ~FE, ~IE);
end procedure;

intrinsic ExteriorDomain(L::SeqEnum : Precision := DefaultPrecision) -> SeqEnum, SeqEnum, SeqEnum
{
    Computes the faces, finite edges and infinite edges of the exterior domain defined by the sheres in L
}
	F := [];
	FE := [];
	IE := [];
	n := #L;

    eps12 := epsilon(1/2,Precision);
    eps13 := epsilon(1/3,Precision);
    eps110 := epsilon(1/10,Precision);
	
    nbdel := 0;

	for s := 1 to n do
		UpdateExteriorDomain(~F, ~FE, ~IE, L[s], 0, ~nbdel, eps12, eps13, eps110);
	end for;
	
	return F,FE,IE;
end intrinsic;

