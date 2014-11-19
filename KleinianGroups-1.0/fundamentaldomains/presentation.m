/*

presentation.m
functions for computing a presentation of a Kleinian group from a fundamental domain

presentation.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../aux.m" : epsilon;
import "../kleinian.m" : kleinianmatrix, isscalar;
import "../geometry/basics.m" : IntersectionAngle, PointInCircle, sqrnorm, scalar, action;
import "../geometry/intervals.m" : PointInInterval;

/*
    INPUT
    a : lower bound of the interval
    b : upper bound of the interval
    f : convex function [a,b] -> R
    eps : maximum error
    k : number of subdivisions (k>2)

    OUTPUT
    c, f(c) = min_[a,b](f)
*/
function Minim(a,b,f,eps,k) //k ge 3
 if Abs(b-a) le eps then
  return (a+b)/2,f((a+b)/2);
 else
  step := (b-a)/k;
  mini := f(a);
  minic := a;
  c := a+step;
  while c le b do
   fc := f(c);
   if fc lt mini then
    minic := c;
    mini := fc;
   end if;
   c +:= step;
  end while;
  return Minim(Max(a,minic-step),Min(b,minic+step),f,eps,k);
 end if;
end function;

/*
    INPUT
    I : [a1,b1,a2,b2,...] describing a union of intervals [a1,b1] U [a2,b2] U ...
    f : a function I -> R, convex on each [ai,bi]
    eps : maximum error
    k : number of subdivisions (k>2)

    OUTPUT
    x, f(x) = min_I(f)
*/
function MinimInterv(I,f,eps,k)
 minix := I[1];
 minif := f(minix);
 n := #I;
 i := 1;
 while i+1 le n do
  x,fx := Minim(I[i],I[i+1],f,eps,k);
  if fx lt minif then
   minix := x;
   minif := fx;
  end if;
  i +:= 2;
 end while;
 return minix,minif;
end function;

/*
    e : edge of a polyhedron
    eps : maximum error
    k : number of subdivisions (k>2)

    OUTPUT
    |x|^2 = min_e |.|^2, x
*/
function MinimEdge(e,eps,k)
 theta,d := MinimInterv(e[2],func<theta|sqrnorm(PointInCircle(e[1],theta))>,eps,k);
 return d, PointInCircle(e[1],theta);
end function;

/*
    INPUT
    FE : finite edges of a polyhedron
    pr : precision
    
    OUTPUT
    partition of FE into potential cycles, according to their minimal distance to 0

    REMARK
    Currently not used (too slow)
*/
function PotentialCycles(FE,pr)
    vprint Kleinian, 2: "Computing potential cycles";
    t := Cputime();
    eps := epsilon(1/25, pr);
    epsbig := epsilon(1/28, pr);
    nfe := #FE;
    distances := [MinimEdge(e,eps,5) : e in FE];
    index := [1..nfe];
    ParallelSort(~distances,~index);

    potentialcycles := [];
    i := 1;
    while i le nfe do
        potcyc := {index[i]};
        while i+1 le nfe and Abs(distances[i]-distances[i+1]) le epsbig do
            i +:= 1;
            Include(~potcyc, index[i]);
        end while;
        Append(~potentialcycles, potcyc);
        i +:= 1;
    end while;

    vprint Kleinian, 3 : "time potential cycles :", Cputime(t);
    return potentialcycles;
end function;

/*
    INPUT
    F : faces of the exterior domain
    FE : finite edges of the exterior domain
    pairing : F[pairing[i]] is the face paired with F[i]
    cycles : reference for storing the cycles
    words : reference for storing the words
    pr : precision
    usedist : boolean indicating whether PotentialCycles should be used

    Computes the cycles of the exterior domain : the list of edges, the cycle transformation, the corresponding word.
*/
procedure ComputeCycles(F,FE,pairing,~cycles,~words,pr,usedist)
eps := epsilon(1/3,pr);
one := Parent(F[1]`g)!1;
pi := Pi(RealField(pr div 3));
visited := [0 : e in FE]; //index of the face whose pairing transfo is used to send the edge to the next one. 0 : not visited yet ; -1 : not paired.
cycles := [];
words := [];
nfe := #FE;

if usedist then
    potentialcycles := PotentialCycles(FE,pr);
else
    potentialcycles := [{1..nfe}];
end if;

for potcyc in potentialcycles do
    restecyc := potcyc;
    while not IsEmpty(restecyc) do
        e := Rep(restecyc);
        if visited[e] eq 0 then
            cycle := [];
            word := [];
            e1 := e;
            f := Rep(FE[e][3]);
            cycletransfo := one;
            
            repeat 
                Append(~cycle, e1);
                f1 := Rep(FE[e1][3]);
                f2 := Rep(FE[e1][3] diff {f1});
                if isscalar( (F[f]`g)*(F[f1]`g) ) then
                    f1 := f2;
                end if;
                f := f1;

                cycletransfo := F[f]`g * cycletransfo;
                Append(~word, f);
                vprint Kleinian, 3 : "word", #word;

                theta := PointInInterval(FE[e1][2]);
                z := PointInCircle(FE[e1][1], theta);
                z1 := action(F[f]`Matrix,z);

                candidates := SetToSequence(restecyc meet F[pairing[f]]`Edges);
                ncan := #candidates;
                can := 1;
                found := false;
                while can le ncan and not found do
                    cir := FE[candidates[can]][1];
                    if Abs(sqrnorm(z1-cir`Center) - (cir`Radius)^2) le eps and Abs(scalar(z1-cir`Center,cir`e3)) le eps then
                        found := true;
                    else
                        can +:= 1;
                    end if;
                end while;

                if not found then
		vprint Kleinian, 1 : "candidates", ncan;
                    error "did not find an adequate edge !";
                end if;

                visited[e1] := f;
                e1 := candidates[can];
            until e1 eq e; 
            
            for e1 in cycle do
                Exclude(~restecyc, e1);
            end for;
            Append(~cycles, <cycle,cycletransfo>);
            Append(~words, word);
        else
	  vprint Kleinian, 1 : "Should not happen, please report." ;
            Exclude(~restecyc, e);
        end if;
    end while;
end for;
vprint Kleinian, 3 : "cycles", cycles, "words", words;
end procedure;

function order(g)
	B := Parent(g);
	if isscalar(g) then
		return 1;
	elif Trace(g)^2-4*Norm(g) eq 0 then
		return 0;
	else
		o := 1;
		gg := g;
		while not isscalar(gg) do
			gg *:= g;
			o +:= 1;
		end while;
		return o;
	end if;
end function;

intrinsic Presentation(F :: SeqEnum, FE :: SeqEnum, O :: AlgAssVOrd : UseDist := false) -> GrpFP, SeqEnum
{
    Computes a finite presentation for the subgroup of B* / Z(B)* with fundamental domain having faces F and edges FE. Returns a finitely presented group G and a list of elements of B* corresponding to the generators of G.
}
    vprint Kleinian, 1 : "Computing the presentation.";
	B := Algebra(O);
	H := B`KlnH;
	pr := Precision(BaseField(H));
    eps := epsilon(1/2, pr);
    zero := H!0;
	cycles := [];
	words := [];
	nf := #F;
	Fr := FreeGroup(nf);
	rels := [];
    pairing := [1..nf];

    distances := [sqrnorm(f`Center) : f in F];
    index := [1..nf];
    ParallelSort(~distances, ~index);
    
    potentialinverses := [];
    i := 1;
    while i le nf do
        potinv := [index[i]];
        while i+1 le nf and Abs(distances[i]-distances[i+1]) le eps do
            i +:= 1;
            Append(~potinv, index[i]);
        end while;
        Append(~potentialinverses, potinv);
        i +:= 1;
    end while;

    for potinv in potentialinverses do
        npi := #potinv;
        for g1 := 1 to npi do
            for g2 := g1 to npi do
                ig1 := potinv[g1];
                ig2 := potinv[g2];
                if isscalar(F[ig1]`g*F[ig2]`g) then
                    Append(~rels, Fr.ig1*Fr.ig2);
                    pairing[ig1] := ig2;
                    pairing[ig2] := ig1;
                end if;
            end for;
        end for;
    end for;

	ComputeCycles(F,FE,pairing,~cycles,~words,pr,UseDist);

	nword := #words;
	for iw := 1 to nword do
		w := words[iw];
		transfo := cycles[iw][2];
		rel := Fr!1;
		lw := #w;
		for i := 1 to lw do
			rel := Fr.w[i] * rel;
		end for;
		ord := order(transfo);
		if ord ne 0 then
			Append(~rels, rel^ord);
		end if;
	end for;
	
	return quo<Fr | rels>, [F[i]`g : i in [1..nf]];
end intrinsic;

function EvaluateWord(w, Gens)
    g := Parent(Gens[1])!1;
    sw := Eltseq(w);
    for i := 1 to #sw do
        g := g*(Gens[Abs(sw[i])]^(Sign(sw[i])));
    end for;
    return g;
end function;

intrinsic LiftPresentation(Pres :: GrpFP, Gens :: SeqEnum, O :: AlgAssVOrd, normone :: BoolElt) -> GrpFP, SeqEnum
{
    Lifts a presentation of a finitely generated subgroup G of B* from a presentation Pres and generators Gens for G/Z(G). G is the norm one group (normone=true) or the unit group (normone=false) of the order O. Returns a finitely presented group G and a list of elements of B* corresponding to the generators of G.
}

    B := Algebra(O);
    K := BaseField(B);
    ZK := Integers(K);
    U,f := UnitGroup(ZK); 
    fi := f^(-1);
    if normone then
        G := sub<U | fi(K!-1)>;
    else
        G := U;
    end if;

    nf := #Gens;
    nu := #Generators(G);
    ng := nf+nu;
    Fr := FreeGroup(ng);
    rels := [(Fr.(nf+1))^Order(G.1)];

    for i := nf+1 to ng do
        for j := 1 to i-1 do
            Append(~rels, Fr![-i,-j,i,j]);
        end for;
    end for;

    for r in Relations(Pres) do
        srel := Eltseq(LHS(r));

        if normone then
            urel := EvaluateWord(LHS(r), Gens);
            if urel eq 1 then
                mul := One(Fr);
            else
                mul := Fr.(nf+1);
            end if;
            Append(~rels, Fr!srel * mul);
        else
            urel := fi(EvaluateWord(LHS(r),Gens));
            useq := Eltseq(urel);
            Append(~rels, Fr!srel * &*[(Fr.(nf+i))^(-useq[i]) : i in [1..nu]]);
        end if;
    end for;

    return quo<Fr | rels>, Gens cat [f(G.j) : j in [1..nu]];
end intrinsic;

