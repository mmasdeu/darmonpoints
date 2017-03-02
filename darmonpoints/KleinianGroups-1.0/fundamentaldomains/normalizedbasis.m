/*

normalisedbasis.m
functions implementing the Normalized Basis Algorithm for computing a Dirichlet domain for a Kleinian group

normalizedbasis.m is part of KleinianGroups, version 1.0 of September 25, 2012
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../geometry/basics.m" : IsometricSphere, EndPoints, PointInCircle, sqrnorm, action, ZerotoP, Circle;
import "../geometry/exteriordomains.m" : UpdateExteriorDomain, IsInExteriorDomain, IntervalOfCircle;
import "../aux.m" : PrintSizeExtDom, epsilon;
import "../geometry/intervals.m" : PointInInterval, LengthInterval;
import "../geometry/volumes.m" : PolyhedronVolume, PolyhedronArea, ComputeZetas, VolumeDisc;
import "../geometry/random.m" : RadiusDisc, RadiusBall, RandomHyperbolicDisc, RandomHyperbolicBall, RandomInInterval, randprod;
import "enumeration.m" : InitializeLattice, Enumerate;
import "../kleinian.m" : kleinianmatrix, isscalar, Hdef, Rdef, DefaultPrecision;

function CheckTimeOut()
  return false;
//  if Cputime() gt 120 then
//  error Error("Time Out");
//  end if;
//return false;
end function;

/*
    Returns the normalized boundary of the exterior domain with faces F
*/
function NormalizedBoundary(F)
	return [f`g : f in F];
end function;

/*
    INPUT
    g : an element of the group
    F : a reference to the faces of the current exterior domain
    FE : a reference to the finite edges of the current exterior domain
    IE : a reference to the infinite edges of the current exterior domain
    eps12 : a small value for controlling approximation, 10^(-pr/2)
    eps13 : a small value for controlling approximation, 10^(-pr/3)
    eps110 : a small value for controlling approximation, 10^(-pr/10)

    Adds g to the normalized boundary of the exterior domain, for the routine KeepSameGroup
*/
procedure AddKSG(g, ~F, ~FE, ~IE, eps12, eps13, eps110)
    nbdel := 0;
    s := IsometricSphere(g,eps12);
    UpdateExteriorDomain(~F, ~FE, ~IE, s, 0, ~nbdel, eps12, eps13, eps110);
    
    s := IsometricSphere(g^(-1),eps12);
    UpdateExteriorDomain(~F, ~FE, ~IE, s, 0, ~nbdel, eps12, eps13, eps110);
end procedure;

/*
    INPUT
    G : a reference to the normalized boundary of the current exterior domain
    F : a reference to the faces of the current exterior domain
    FE : a reference to the finite edges of the current exterior domain
    IE : a reference to the infinite edges of the current exterior domain
    eps12 : a small value for controlling approximation, 10^(-pr/2)
    eps13 : a small value for controlling approximation, 10^(-pr/3)
    eps110 : a small value for controlling approximation, 10^(-pr/10)

    Runs the routine KeepSameGroup
*/
procedure KeepSameGroup(~G,~F,~FE,~IE,eps12, eps13, eps110)
vprint Kleinian: "=========== KeepSameGroup";
S := SetToSequence(G);
repeat
    add := 0;
	for gamma in S do
		_,delta := Reduce(gamma, F : eps12 := eps12, Word := false);
		gammabar := delta*gamma;
		if not isscalar(gammabar) then
            add +:= 1;
            AddKSG(gammabar, ~F, ~FE, ~IE, eps12, eps13, eps110);
		end if;
	end for;
    vprint Kleinian, 2: "successful reductions :", add;
	PrintSizeExtDom(F,FE,IE);
    S := NormalizedBoundary(F);
until add eq 0;
G := SequenceToSet(S);
end procedure;

/*
    INPUT
    g : an element of the group
    F : a reference to the faces of the current exterior domain
    FE : a reference to the finite edges of the current exterior domain
    IE : a reference to the infinite edges of the current exterior domain
    e : a reference to the index of an edge intersecting Int(g) (optional : 0=none, currently not used)
    G : a reference to the normalized boundary of the current exterior domain
    eps12 : a small value for controlling approximation, 10^(-pr/2)
    eps13 : a small value for controlling approximation, 10^(-pr/3)
    eps110 : a small value for controlling approximation, 10^(-pr/10)

    Adds g to the normalized boundary of the exterior domain, for the routine CheckPairing
*/
procedure AddP(g, ~F, ~FE, ~IE, ~e, ~G, eps12, eps13, eps110)
    nbdel := e;
    s := IsometricSphere(g,eps12);
	UpdateExteriorDomain(~F, ~FE, ~IE, s, /*e,*/0, ~nbdel, eps12, eps13, eps110);
    Include(~G,g);
    e -:= nbdel;

    nbdel := e;
    s := IsometricSphere(g^(-1), eps12);
	UpdateExteriorDomain(~F, ~FE, ~IE, s, 0, ~nbdel, eps12, eps13, eps110);
    Include(~G, g^(-1));
    e -:= nbdel;
end procedure;

/*
    INPUT
    G : a reference to the normalized boundary of the current exterior domain
    F : a reference to the faces of the current exterior domain
    FE : a reference to the finite edges of the current exterior domain
    IE : a reference to the infinite edges of the current exterior domain
    allpaired : a reference for storing a boolean indicating whether the exterior domain has a face pairing
    eps12 : a small value for controlling approximation, 10^(-pr/2)
    eps13 : a small value for controlling approximation, 10^(-pr/3)
    eps110 : a small value for controlling approximation, 10^(-pr/10)

    OPTIONAL
    Method : repairing method : Reduction | LengthThree

    Runs the routine CheckPairing
*/
procedure CheckPairing(~G,~F,~FE,~IE,~allpaired,eps12,eps13,eps110 : Method := "Reduction")
vprint Kleinian: "=========== CheckPairing :", Method, "method";
allpaired := true;
repairing := 0;
ie := 1;
nfe := #FE;
while ie le nfe and ie le #FE do
    e := FE[ie];
	if Method eq "Reduction" then
		Sz1 := EndPoints(e);
		Sz := {z : z in Sz1 | sqrnorm(z) lt 1-eps110};
		if #Sz lt 2 then
			theta := PointInInterval(e[2]);
			z1 := PointInCircle(e[1], theta);
			Include(~Sz, z1);
		end if;
            if #Sz ne 0 and not IsInExteriorDomain(Rep(Sz),F,eps110) then
                error "===========  INVALID EDGE !!!!!";
            end if;
		for z1 in Sz do
			for f in e[3] do
                if f le #F and ie gt 0 then
                    gamma := F[f]`g;
                    if not IsInExteriorDomain(action(F[f]`Matrix , z1), F, eps110) then
                        allpaired := false;
                        _, delta := Reduce(gamma, F : eps12 := eps12, z := z1, Word := false);
                            gamma := delta*gamma;
                            if not isscalar(gamma) then
                                repairing +:= 1;
                                AddP(gamma, ~F, ~FE, ~IE, ~ie, ~G, eps12, eps13, eps110);
                            end if;
                    end if;
                end if;
			end for;
		end for;
	elif Method eq "LengthThree" then
		Faces := SetToSequence(e[3]);
		g1 := F[Faces[1]]`g;
		g2 := F[Faces[2]]`g;
		gamma := g1 * g2^(-1);
        found := false;
        for g in G do
            if isscalar(gamma*g^(-1)) then
                found := true;
                break;
            end if;
        end for;
		if not isscalar(gamma) and not found then
			if not isscalar(g1*g2) then
				allpaired := false;
                repairing +:= 1;
			end if;
            AddP(gamma, ~F, ~FE, ~IE, ~ie, ~G, eps12, eps13, eps110);
		end if;
	else
		error "Invalid Pairing Method";
	end if;
    ie +:= 1;
end while;
vprint Kleinian, 2: "allpaired", allpaired, "--- repairing :", repairing;
PrintSizeExtDom(F,FE,IE);
end procedure;

intrinsic myIndex(LG :: SeqEnum, InSubgroup :: UserProgram) -> RngIntElt, SeqEnum, SeqEnum
{
    Returns the index, a set of left cosets and a set of generators, of the finite index subgroup G' in G, where G is generated by LG and InSubgroup tests whether an element is in G'.
}
  B := Parent(LG[1]);
  S1 := [One(B)];
  S1new := [One(B)];
  S2 := {B |};
    while not S1new cmpeq []  do

      S1next := [];

      for s in S1new do
        for g in LG do
          x := s*g;
          insg := false;

          for t in (S1 cat S1next) do
            if InSubgroup(x*t^(-1)) then
                insg := true;
			    Include(~S2,x*t^(-1));
            end if;
          end for;

          if not insg then
            Append(~S1next,x);
          end if; 

        end for; 
      end for; 

      S1 cat:= S1next;
      S1new := S1next;

    end while;
    S3 := SetToSequence(S2);
  return #S1, S1, S3; 
end intrinsic;

/*
    INPUT
    g : an element of the group
    F : a reference to the faces of the current exterior domain
    FE : a reference to the finite edges of the current exterior domain
    IE : a reference to the infinite edges of the current exterior domain
    G : a reference to the normalized boundary of the current exterior domain
    eps12 : a small value for controlling approximation, 10^(-pr/2)
    eps13 : a small value for controlling approximation, 10^(-pr/3)
    eps110 : a small value for controlling approximation, 10^(-pr/10)

    Adds g to the normalized boundary of the exterior domain, for the main procedure
*/
procedure AddNB(g, ~F, ~FE, ~IE, ~G, eps12, eps13, eps110)
    nbdel := 0;
    Include(~G, g);
    s := IsometricSphere(g,eps12);
    UpdateExteriorDomain(~F,~FE,~IE, s, 0, ~nbdel, eps12, eps13, eps110);

    Include(~G, g^(-1));
    s := IsometricSphere(g^(-1),eps12);
    UpdateExteriorDomain(~F,~FE,~IE, s, 0, ~nbdel, eps12, eps13, eps110);
end procedure;

function CommUnits(O,x)
  L := [];
  B := Algebra(O);
  F := BaseField(B);
  cp := CharacteristicPolynomial(x);
  if not IsIntegral(x) or not IsIrreducible(cp) then return []; end if;
  K<t> := ext<F | cp>;
  ZK := AbsoluteOrder(MaximalOrder(K));
  Kabs := NumberField(ZK);
  tabs := Kabs!t;
  _ := ClassGroup(ZK : Proof := "Subgroup");
  try
    OK := Order([tabs]);
  catch e
    return [];
  end try;
  if Norm(Conductor(OK)) gt 3*10^6 then return []; end if;
  U,f := UnitGroup(OK : Al := "ClassGroup");
  for g in Generators(U) do
  if Order(g) eq 0 then
    s := Eltseq(K!(Kabs!f(g)));
    y := s[1] + s[2]*x;
    Append(~L, y);
  end if;
  end for;
  return L;
end function;

intrinsic NormalizedBasis(O :: AlgAssVOrd : InitialG := [], NbEnum := 0, PeriodEnum := 100, Level := 1, BoundPrimes := -1, PairingMethod := "Reduction", GroupType := "NormOne", EnumMethod := "SmallBalls", Maple := false, zetas := [], zK2 := 0, Center := "Auto", index := 1, pr := DefaultPrecision, max_time := 0) -> SeqEnum, SeqEnum, SeqEnum, SeqEnum, FldReElt, SeqEnum, SeqEnum, FldReElt, FldReElt, FldReElt, RngIntElt, RngIntElt, AlgQuatElt
{
    Computes a fundamental domain for the Kleinian group attached to the order O.

    Returns the normalized boundary of the domain, the faces, the finite edges, the infinite edges, the volume, elements with prime norm, the time spent enumerating, the time spent repairing, the time spent in KeepSameGroup, the number of enumerated vectors, the number of enumerated group elements.
}
nbit := 0;
if EnumMethod notin {"BigBall", "ManyBalls", "SmallBalls", "None"} then
    error "Invalid Enumeration Method.";
end if;

if max_time eq 0 then
    max_time := Infinity();
end if;
TimeLimit:=Cputime() + max_time;

if GroupType eq "NormOne" then
    grouptype := 1;
elif GroupType eq "Units" then
    grouptype := 2;
elif GroupType eq "Maximal" then
    grouptype := 3;
    if not IsMaximal(O) then
        vprint Kleinian, 1 : "Warning : computing the normalizer of a non-maximal order, may have unexpected behaviour.";
    end if;
else
    error "Invalid Group Type";
end if;

//if GroupType ne "NormOne" then
//  vprint Kleinian, 2: "\ncomputing some units first\n";
//  found := false;
//  moreunits := [];
//  for x in ZBasis(O) do
//    newunits := CommUnits(O,x);
//    moreunits cat:= newunits;
//    for g in newunits do
//      if not IsSquare(Norm(g)) then found := true; break; end if;
//    end for;
//    if found then break; end if;
//  end for;
//  InitialG cat:= moreunits;
//end if;

if pr ne DefaultPrecision then
    R := RealField(pr);
    H := QuaternionAlgebra<R|-1,-1>;
else
    H := Hdef;
    R := Rdef;
end if;

if Center cmpeq "J" then
    Center := H!0;
elif Center cmpeq "Auto" then
    Center := 17/5*H.2 - 1/2*H.1 + 1/3*H![1,0,0,0];
end if;

B := Algebra(O);
K := BaseField(B);
ZK := MaximalOrder(K);
degK := Degree(K);

_,_,Fuchsian := KleinianInjection(B : Center := Center, H := Parent(Center), Redefine := true);

omega := K!ZK.2;

primes := [ B | ];
try

if Type(Level) eq RngIntElt then
	if not IsMaximal(O) then
		vprint Kleinian: "========= ========= Computing for a maximal order first";
		OO := MaximalOrder(O);
		LG,_,_,_,_,primes := NormalizedBasis(OO : InitialG := InitialG, NbEnum := NbEnum, PeriodEnum := PeriodEnum, BoundPrimes := BoundPrimes, PairingMethod := PairingMethod, GroupType := GroupType, EnumMethod := EnumMethod, zetas := zetas, Maple := false, zK2 := zK2, Center := Center, pr := pr);
		index, Repres, Genes := myIndex(LG, func<x | x in O>);
		vprintf Kleinian, 2: "========= ========= Subgroup has index %o in larger group, %o generators found\n", index, #Genes;
		vprint Kleinian: "========== ========== Computing for the smaller order";
		InitialG := InitialG cat Genes;
		NbEnum := 1;
	end if;
end if;

vprint Kleinian: "========== NormalizedBasis";
H := B`KlnH;
e := H![1,0,0,0];
MH := Parent(Matrix(2, [H| e, 0, 0, e]));
R := BaseField(H);
pr := Precision(R);
period := 1;

eps12 := epsilon(1/2,pr);
eps13 := epsilon(1/3,pr);
eps110 := epsilon(1/10,pr);

loo := R!7;


vprint Kleinian: "=========== Initialization";

indexunits := 1;
randids := [];
if grouptype ge 2 then
   vprint Kleinian: "Computing the unit index";
   if grouptype eq 2 then
       U,f := UnitGroup(ZK); 
   else
       Ramf, Ramoo := Discriminant(B);
       U,f := SUnitGroup(Ramf);
   end if;
   ngu := Ngens(U);
   vprint Kleinian, 3 : "Unit group computed";
   pm := AbelianGroup([2]);
   Lhom := [hom<U -> pm | [pm!((1-Sign(Evaluate(K!f(U.i),v))) div 2) : i in [1..ngu]]> : v in RealPlaces(K)];
   Lker := [Kernel(hu) : hu in Lhom]; 
   if Lker eq [] then
       Utotpos := U;
   else
       Utotpos := &meet Lker;
   end if;
   U2 := sub<Utotpos | [Utotpos!(2*gene) : gene in Generators(U)]>;
   indexunits *:= Index(Utotpos, U2);
   vprint Kleinian, 2 : "index due to units :", Index(Utotpos, U2);
   if grouptype eq 3 then
       Cl, f := ClassGroup(K);
       if Ramoo cmpeq [] then
           Div := DivisorGroup(K)!0;
       else
           Div := &+[Divisor(v) : v in Ramoo];
       end if;
       Clplus, g := RayClassGroup(Div);
       M1 := sub<Clplus|[(g^(-1))(pp[1]) : pp in Factorization(Ramf)]>;
       J1, proj1 := quo<Clplus|M1>;
       mul2 := hom<J1 -> J1 | [x -> 2*x : x in Generators(J1)]>;
       J12 := Kernel(mul2);
       principality := hom<J12 -> Cl | [x -> (f^(-1))( g( (proj1^(-1))(J1!x) ) ) : x in Generators(J12)]>;
       M2 := Kernel(principality);
       ClB, proj2 := quo<J12 | M2>;
       indexunits *:= #ClB;
       vprint Kleinian, 2 : "index due to class group :", Index(J12, M2);

       ids := [g( (proj1^(-1))( J1 ! (proj2^(-1))(gen) ) ) : gen in Generators(ClB)];
       Append(~ids, Ramf);
       randids := SetToSequence({ idp[1] : idp in Factorization(lideal<O | Generators(idg)>), idg in ids });
       vprint Kleinian, 3 :  "Norms of randomising ideals :", [Norm(Norm(idp)) : idp in randids];
   end if;
   vprint Kleinian, 2: "total index :", indexunits;
end if;

if not Fuchsian then
	vprint Kleinian: "Computing the covolume";
	if Type(Level) ne RngIntElt then
		index *:= Psi(Level);
	end if;
	Covol := R!Covolume(B : zK2 := zK2)*index/indexunits;
	vprint Kleinian, 2: "covolume", RealField(10)!Covol;
else
	vprint Kleinian: "Computing the coarea";
	
	if Type(Level) ne RngIntElt then
		index *:= Psi(Level);
	end if;
	Covol := R!Coarea(B : zK2 := zK2)*index/indexunits;
	vprint Kleinian, 2: "coarea", RealField(10)!Covol, "rational", BestApproximation(Covol/Pi(RealField(50)), 1000);

    Coo := Circle(H!0,R!1,H.1);
end if;

DK := Discriminant(ZK);
DB := RamifiedPlaces(B);
if #DB ne 0 then
	db := &*[Norm(p) : p in DB];
else
	db := 1;
end if;
disc := Abs(R!(DK^4*db^2));
vprint Kleinian, 3: "disc", RealField(5)!disc;

if NbEnum eq 0 then
    NbEnum := Floor(0.3*Covol*Log(2+Covol))+1;//Floor(1.5*Covol)+1;
end if;
if degK eq 2 and db eq 1 then
    NbEnum *:= 2;
end if;
if EnumMethod eq "ManyBalls" then
    NbEnum div:= 4;
    NbEnum +:= 1;
end if;
vprint Kleinian, 3: "NbEnum = ", NbEnum;

if not Fuchsian and zetas eq [] then
    zetas := ComputeZetas(pr);
end if;

F := [];
FE := [];
IE := [];

Enum := {};

if Fuchsian then
	denomfactor := 1;
else
	denomfactor := 5000;
end if;

factor := R!(Max(Floor(disc*index/denomfactor),1/2)); //index should actually be the index of the orders here.
vprint Kleinian, 3: "factor :", factor;

propi := 6;
u := 0;
stepu := 4*factor;
if EnumMethod eq "SmallBalls" then
    magicmul := 18/10;
    stepu := 4*factor * (magicmul * (disc^(1/2))^(1/(2*degK)) + degK);
end if;
balance := stepu/(4*factor*degK);
vprint Kleinian, 3 : "balance", RealField(10)!balance;

HGM := 0;
basismat := [];
if EnumMethod eq "BigBall" then
    randomized := false;
    InitializeLattice(O, ~Lat, ~TZB, ~nzb, pr, factor, ~HGM, ~basismat : Balance := balance);
    if TZB eq [] then
        return [],[],[],[],0,[],[],0,0,0,0,0,0,0;
    end if;
end if;

if EnumMethod eq "ManyBalls" or EnumMethod eq "SmallBalls" then
    vprint Kleinian: "Computing radius for random centers";
    if Fuchsian then
        radenum := RadiusDisc(10*Max(Covol^(2+1/10),R!2));
    else
        radenum := RadiusBall(10*Max(Covol^(2+1/10),R!2), eps110);
    end if;
    vprint Kleinian, 3: "radenum", RealField(5)!radenum;
else
    radenum := R!0;
end if;

divadapt := 9/10;

totalvect := 0;
totalgpelt := 0;

allpaired := false;
Vol := 0;

G := {};

nochange := 0;

enumtime := Cputime();
enumtime *:= 0;
pairingtime := enumtime;
ksgtime := enumtime;
elapsed_time := Cputime();

repeat
	nbit +:= 1;
	period -:= 1;
	if period le 0 then
        if EnumMethod ne "None" then
		t := Cputime();
        if EnumMethod eq "ManyBalls" then
            nbballs := NbEnum;
            localnbenum := 1;
            finboucle := func<b,nb | b gt nbballs>;
        elif EnumMethod eq "SmallBalls" then
            nbballs := 0;
            localnbenum := 0;
            finboucle := func<b,nb | nb ge NbEnum>;
            if Fuchsian then
                Ioo := IntervalOfCircle(Coo,F,false,{},eps12);
                loo := LengthInterval(Ioo);
            end if;
        elif EnumMethod eq "BigBall" then
            nbballs := 1;
            localnbenum := NbEnum;
            finboucle := func<b,nb | true>;
        end if;
        Enum := {};
        if EnumMethod eq "ManyBalls" or EnumMethod eq "SmallBalls" then
            vprint Kleinian, 3: "radenum", RealField(5)!radenum;
        end if;
        ball := 1;
        oldtotalgpelt := totalgpelt;
        vprint Kleinian: "========= Enumerate";
        vprint Kleinian, 3: "stepu =", RealField(5)!stepu;
        repeat
            allowsq := true;
            if EnumMethod eq "ManyBalls" or EnumMethod eq "SmallBalls" then
                if ball mod 10 lt propi and #IE ne 0 and (not Fuchsian or loo gt eps13) then
                    allowsq := false;
                    if Fuchsian then
                        enumcenter := RandomHyperbolicDisc(H,radenum/2);
                        theta := Random(Ioo);
                        x := PointInCircle(Coo, theta);
                    else
                        enumcenter := RandomHyperbolicBall(H,radenum/4,eps110);
                        ed := Random(1,#IE);
       	                theta := PointInInterval(IE[ed][2]);
                     	x := PointInCircle(IE[ed][1], theta);
                    end if;
                    x := (1-Exp(-radenum))*x;
                    hx := ZerotoP(x,MH);
                    enumcenter := action(hx, enumcenter);
                    vprintf Kleinian, 2: "i";
                else
                    vprintf Kleinian, 2: "r";
                    if Fuchsian then
                        enumcenter := RandomHyperbolicDisc(H,radenum);
                    else
                        enumcenter := RandomHyperbolicBall(H,radenum,eps110);
                    end if;
                end if;
                if (#IE eq 0 or (Fuchsian and loo ge eps13)) and #F ne 0 then
                    rbound := 2;
                else
                    rbound := 6;
                end if;
                if grouptype eq 3 and #randids ne 0 and Random(rbound) eq 0 then
                    randid := randprod(randids);
                    savHGM := HGM;
                    HGM := 0;
                    savbasismat := basismat;
                    basismat := [];
                    nab := (R!Norm(Norm(randid)))^(1/degK);
                    vprintf Kleinian, 3 : "{%o}", Norm(Norm(randid));
                    randomized := true;
                    stepu *:= nab;
                else
                    randid := O;
                    randomized := false;
                end if;
                InitializeLattice(randid, ~Lat, ~TZB, ~nzb, pr, factor, ~HGM, ~basismat : Center1 := enumcenter, Balance := balance);
                if TZB eq [] then
                    return [],[],[],[],0,[],[],0,0,0,0,0,0,0;
                end if;
                u := 0;
            end if;
            Enumerate(~Enum,~u,TZB,nzb,~Lat,~totalvect,~totalgpelt, localnbenum, ~stepu, O, factor, ~primes, ZK, BoundPrimes, grouptype, allowsq,~divadapt,Fuchsian,randomized);
            if randomized then
                HGM := savHGM;
                basismat := savbasismat;
                stepu /:= nab;
            end if;
            ball +:= 1;
        until finboucle(ball, totalgpelt-oldtotalgpelt);
	    vprintf Kleinian, 2: "\nTOTAL : %o enumerated vectors --- ", totalvect;
    	vprintf Kleinian, 2: "%o group elements (%o %%)\n", totalgpelt, RealField(5)!(100*totalgpelt/Max(totalvect,1));
	    vprint Kleinian, 3: "CPU time for enumeration: ", Cputime(t), " --- stepu =", RealField(5)!stepu;
		enumtime +:= Cputime(t);
        end if;
		
        for g in InitialG do
            if not isscalar(g) then
                Include(~Enum, g);
            end if;
        end for;

        for ied in IE do
            ieg := F[Rep(ied[3])]`g;
            if Trace(ieg)^2 eq 4*Norm(ieg) then
                vprint Kleinian, 3 : "Bianchi helper";
                x := ieg[1];
                y := ieg[3]-ieg[4];
                gamma := B![1,x*y,(y^2-x^2)/2,(x^2+y^2)/2];
                Include(~Enum, gamma);
                AddNB(gamma, ~F, ~FE, ~IE, ~G, eps12, eps13, eps110);
                gamma := B![1,x*y*omega,(y^2-x^2)*omega/2,(x^2+y^2)*omega/2];
                Include(~Enum, gamma);
                AddNB(gamma, ~F, ~FE, ~IE, ~G, eps12, eps13, eps110);
            end if;
        end for;
		
        vprint Kleinian: "Reduction of the new elements";
		for gamma in Enum do
			vprint Kleinian: "gamma = ", gamma;
			if #F ne 0  and PairingMethod ne "None" then
				_, delta := Reduce(gamma, F : eps12 := eps12, Word := false);
				gammabar := delta*gamma;
			else
				gammabar := gamma;
			end if;
			if not isscalar(gammabar) and not (gammabar in G) then
			   vprint Kleinian: "About to call AddNB";
                           AddNB(gammabar, ~F, ~FE, ~IE, ~G, eps12, eps13, eps110);
			   vprint Kleinian: "Done AddNB";

			end if;
		end for;
		PrintSizeExtDom(F,FE,IE);
		period := PeriodEnum;
        vprint Kleinian: "Done with Reduction of the new elements";

    	t := Cputime();
	    KeepSameGroup(~G,~F,~FE,~IE,eps12, eps13, eps110);
    	ksgtime +:= Cputime()-t;
	end if;
	
	anf := #F;
	anfe := #FE;
	anie := #IE;

	t := Cputime();
	if PairingMethod eq "None" then
		allpaired := true;
	else
		CheckPairing(~G,~F,~FE,~IE,~allpaired,eps12,eps13,eps110 : Method := PairingMethod);
	end if;
	pairingtime +:= Cputime()-t;

    if not allpaired and #IE eq 0 and nochange le 1 then
        period +:= 1;
    end if;
	
	if #F eq anf and #FE eq anfe and #IE eq anie then
		period := 1;
		nochange +:= 1;
        propi := Min(propi+1,7);
	else
		nochange := 0;
        propi := Max(propi-1,3);
	end if;
	
    radenum +:= R!1/6;
    if #FE ne 0 then
        radenum +:= 1/5;
    end if;
	if nochange mod /*6 eq 4*/10 eq 9 then
		NbEnum *:= 2;
        //radenum +:= 1/8;
		vprint Kleinian, 3: "NbEnum :", NbEnum;
	end if;
	if nochange mod /*3 eq 2*/5 eq 4 then
		NbEnum *:= 2;
        //radenum +:= 1/8;
		vprint Kleinian, 3: "NbEnum :", NbEnum;
	end if;
	
	vprint Kleinian: "========= IsSubgroup";
	if not Fuchsian then
		if #F ne 0 and #IE /*eq 0*/ le 1 then
			if allpaired then
				Vol := PolyhedronVolume(F,FE, zetas);
				vprintf Kleinian: "subgroup of index %o (%o)\n", Round(Vol/Covol), RealField(6)!(Vol/Covol);
                vprint Kleinian, 3 : "Vol", Vol, "\nCov", Covol;
		else
				vprint Kleinian: "polyhedron is not a fundamental domain";
			end if;
		else
			vprint Kleinian: "polyhedron with infinite volume";
		end if;
        vprint Kleinian: "estimated progress:", RealField(5)!(50*Min(#F,3*Covol)/(3*Covol) + 50 - 50*Min(#IE,1+#F)/(1+#F)), "%";
	else //fuchsian
        Ioo := IntervalOfCircle(Coo,F,false,{},eps12);
        loo := LengthInterval(Ioo);
        vprint Kleinian, 2: "length at infinity =", 50*loo/Pi(RealField(5)), "%";
		if #F ne 0 and loo le eps13 then
			if allpaired or nochange ge 5 then
				Vol := PolyhedronArea(F,FE);
				vprintf Kleinian: "subgroup of index %o (%o)\n", Round(Vol/Covol), RealField(6)!(Vol/Covol);
			else
				vprint Kleinian: "polyhedron is not a fundamental domain";
			end if;
		else
			vprint Kleinian: "polygon with infinite area";
		end if;
        vprint Kleinian: "estimated progress:", RealField(5)!(100*(1-loo/(2*Pi(RealField(5))))^2*Min(#F,Covol)/Covol), "%";
	end if;

    if (Vol gt 0 and Vol lt Covol*9999/10000) then
        vprint Kleinian, 1 : "Error in the computation, rebuilding the exterior domain.";
        F,FE,IE := ExteriorDomain(F);
        allpaired := false;
    end if;
    if Fuchsian then
        F,FE,IE := ExteriorDomain(F);
    end if;

until (allpaired and Abs(Vol/Covol-1) lt 1/1000) or Abs(Vol/Covol-1) lt 1/10000000000;

if Maple then
    MapleFile(MapleDraw(MapleExteriorDomain([],FE,IE) : view := 1.), "FinalFDom");
    MapleFile(MapleDraw(MapleExteriorDomain(F,FE,IE) : view := 1.), "FinalFDomS");
    MapleFile(MapleDraw(MapleExteriorDomain([],FE,IE : Caption := true) : view := 1.), "FinalFDomC");
end if;

catch e
 return false,false,false;
end try;

return NormalizedBoundary(F),F,FE,IE,Vol,primes,enumtime,pairingtime,ksgtime,totalvect,totalgpelt,u/(8*factor),Center;

end intrinsic;
