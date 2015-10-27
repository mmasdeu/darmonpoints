/*

kleinian.m
Generic functions for handling arithmetic Kleinian groups

kleinian.m is part of KleinianGroups, version 1.0 of September 25, 2012
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "geometry/basics.m" : JtoP, ZerotoP;

DefaultPrecision := 100;
Rdef := RealField(DefaultPrecision);
epsdef := 10^(-Rdef!DefaultPrecision/2);
Hdef<Idef,Jdef,Kdef> := QuaternionAlgebra<Rdef | -1,-1>;

declare attributes AlgQuat : KlnI, KlnH, KlnV;

declare verbose Kleinian, 2;


/*
    INPUT
    B : a quaternion algebra over a number field
    vC : a split infinite place of the base field of B
    M : the 2*2 matrix ring over C
    MH : the 2*2 matrix ring over the ring of Hamiltonians
    center : the center of the conjugation
    pr : the precision

    OUTPUT
    a corresponding embedding of O into M into MH when normalise=false, and of O* / Z_F* into PSL_2(C) into MH* when normalize=true
*/
function ioo(B,vC,M,MH,center,pr)
	H := BaseRing(MH);
	aa := Evaluate(-Norm(B.1), vC : Precision := pr);
	sa := Sqrt(aa);
	bb := Evaluate(-Norm(B.2), vC : Precision := pr);
	bsa := bb*sa;
	P,Pinv := JtoP(center, M);
	return function(x,normalize) 
		m := Pinv*(M!
			[x1   + x2*sa,	x3 + x4*sa,
			x3*bb - x4*bsa,	x1 - x2*sa]
			)*P
		where x1 := Evaluate(x[1], vC : Precision := pr)
		where x2 := Evaluate(x[2], vC : Precision := pr)
		where x3 := Evaluate(x[3], vC : Precision := pr)
		where x4 := Evaluate(x[4], vC : Precision := pr);
        if normalize and Norm(x) ne 1 then
            scal := 1/Sqrt(Determinant(m));
            m *:= scal;
        end if;
        mat := MH![A,B,C,D] 
		where A := ( (a+Conjugate(d)+(b-Conjugate(c))*H.2) )/2
		where B := ( (b+Conjugate(c)+(a-Conjugate(d))*H.2) )/2
		where C := ( (c+Conjugate(b)+(d-Conjugate(a))*H.2) )/2
		where D := ( (d+Conjugate(a)+(c-Conjugate(b))*H.2) )/2
	  where a := H![Re(m[1,1]),0,0,0] + H.1*Im(m[1,1])
	  where b := H![Re(m[1,2]),0,0,0] + H.1*Im(m[1,2])
	  where c := H![Re(m[2,1]),0,0,0] + H.1*Im(m[2,1])
	  where d := H![Re(m[2,2]),0,0,0] + H.1*Im(m[2,2]);
        return mat;
        end function;
		/*
		Pinv*
		[x[1]+x[2]*Sqrt(a), x[3]+x[4]*Sqrt(a),
		x[3]*b-x[4]*b*Sqrt(a), x[1]-x[2]*Sqrt(a)]
		*P
		*/
end function;

//In the Fuchsian case, it is necessary that a is positive at some real place.
intrinsic KleinianInjection(B :: AlgQuat : Center := 0, H := Hdef, Redefine := false) -> Map,AlgQuat,BoolElt
{
    Initializes and returns an embedding of B into M_2(C) into M_2(H), conjugated according to Center.
    Also returns H and a boolean indicating whether B is Fuchsian or not.
}
if not assigned B`KlnI or Redefine then
	pr := Precision(BaseField(H));
	if Center eq 0 then
		Center := H.2;
	end if;
	F := BaseField(B);
	oo := SequenceToSet(InfinitePlaces(F));
	ooR := SequenceToSet(RealPlaces(F));
	ooC := oo diff ooR;
	_,ooRam := RamifiedPlaces(B);
	require #ooC le 1 : "The base field must have at most one complex place.";
	if #ooC eq 1 then
		require #ooR eq #ooRam : "The quaternion algebra must be ramified at all real places.";
		vC := Rep(ooC);
		fuchsian := false;
	else
		require #ooR eq #ooRam+1 : "The quaternion algebra must be ramified at all real places but one.";
		vC := Rep(ooR diff SequenceToSet(ooRam));
		fuchsian := true;
	end if;

	M := MatrixRing(ComplexField(pr),2);
e := H![1,0,0,0];
MH := Parent(Matrix(2, [H| e, 0, 0, e]));
	B`KlnI := ioo(B,vC,M,MH,Center,pr);
	B`KlnH := H;
    B`KlnV := vC;
end if;
return B`KlnI,B`KlnH, fuchsian;
end intrinsic;

function kleinianmatrix(x : Normalize := true) 
	B := Parent(x);
	if not assigned B`KlnI then
        error "No Kleinian group defined for x.";
    end if;
	return (B`KlnI)(x,Normalize);
end function;

intrinsic KleinianMatrix(x::AlgQuatElt : Normalize := true) -> AlgMatElt
{
    Returns the matrix of the quaternion x acting on the unit ball model of the hyperbolic 3-space.
}
    return kleinianmatrix(x : Normalize := Normalize);
end intrinsic;

function isscalar(x)
    return x eq Conjugate(x);
end function;

function DefiniteNorm(x : Facteur := 1, Center1 := 0, Center2 := 0, m := kleinianmatrix(x : Normalize := false), mready := false, Balance := 1) //represents d(g*Center1, Center2)
    if not mready then
        MR := Parent(m);
        h1 := ZerotoP(Center1, MR);
        _,h2i := ZerotoP(Center2, MR);
        m := h2i*m*h1;
    end if;
    B := Parent(x);
    pr := Precision(BaseField(B`KlnH));
    _,ramplaces := RamifiedPlaces(B);
    if ramplaces cmpeq [] or Balance eq 0 then
        term := 0;
    else
        nx := Norm(x);
        term := &+[Evaluate(nx, v : Precision := pr) : v in ramplaces];
    end if;
	return Facteur*(Norm(m[1,1])+Norm(m[1,2]) + Balance*term);
end function;

function DefiniteBilinearForm(x1, x2 : Facteur := 1, Center1 := 0, Center2 := 0, Balance := 1) //represents d(g*Center1, Center2)
	return Facteur*(DefiniteNorm(x1+x2 : Center1 := Center1, Center2 := Center2, Balance := Balance) - DefiniteNorm(x1: Center1 := Center1, Center2 := Center2, Balance := Balance) - DefiniteNorm(x2: Center1 := Center1, Center2 := Center2, Balance := Balance));
end function;

function dgm(O : Precision := DefaultPrecision, Center1 := 0, Center2 := 0, Facteur := 1, Balance := 1, ComputeHGM := false, HGM := 0, Matrices := [])
	R := RealField(Precision);
	B := Algebra(O);
	gens := ZBasis(O);
	n := #gens;
    if Matrices cmpeq [] then
        Matrices := [kleinianmatrix(gens[i] : Normalize := false) : i in [1..n]];
    end if;
    MR := Parent(Matrices[1]);
    if not ComputeHGM then
        h1 := ZerotoP(Center1, MR);
        _,h2i := ZerotoP(Center2, MR);
        rMatrices := [h2i*Matrices[i]*h1 : i in [1..n]];
    else
        rMatrices := [MR!0 : i in [1..n]];
    end if;
	DGM := MatrixRing(R,n) ! 0;
    for i := 1 to n do
        DGM[i,i] := 2*DefiniteNorm(gens[i] : Facteur := Facteur, Center1 := Center1, Center2 := Center2, m := rMatrices[i], mready := true, Balance := Balance);
    end for;
    for i := 1 to n do
        for j := i+1 to n do
            DGM[i,j] := DefiniteNorm(gens[i]+gens[j] : Facteur := Facteur, Center1 := Center1, Center2 := Center2, m := rMatrices[i]+rMatrices[j], mready := true, Balance := Balance) - (DGM[i,i] + DGM[j,j])/2; 
            DGM[j,i] := DGM[i,j];
        end for;
    end for;

	return DGM+HGM,gens,Matrices;
end function;

intrinsic DefiniteGramMatrix(O :: AlgAssVOrd : Precision := DefaultPrecision, Center1 := 0, Center2 := 0, Facteur := 1, Balance := 1, ComputeHGM := false, HGM := 0, Matrices := []) -> AlgMatElt,SeqEnum,SeqEnum
{
    Returns the Gram matrix of Q and the Z-basis of O with respect to which it was computed. Q is a positive definite quadratic form on O detecting elements sending Center1 close to Center2, scaled by Facteur.
} //represents d(g*Center1, Center2)
    return dgm(O : Precision := Precision, Center1 := Center1, Center2 := Center2, Facteur := Facteur, Balance := Balance, ComputeHGM := ComputeHGM, HGM := HGM, Matrices := Matrices);
end intrinsic;

intrinsic Covolume(B :: AlgQuat : Precision := DefaultPrecision div 10, zK2 := 0) -> FldReElt
{
    The covolume of the Kleinian group attached to a maximal order in B. The optional argument zK2 is the value at 2 of the Dedekind zeta function of the base field.
}
	R := RealField(Precision);
	pi := Pi(R);
	K := BaseField(B);
	ZK := MaximalOrder(K);
	DK := Discriminant(ZK);
    if zK2 eq 0 then
    	zK := LSeries(K : Precision := Precision);
	    zK2 := Evaluate(zK,2);
    end if;
	DB := RamifiedPlaces(B);
	if #DB ne 0 then
		phi := &*[Norm(p)-1 : p in DB];
	else
		phi := 1;
	end if;
	n := Degree(K);

	return Abs(R!DK)^(3/2) * zK2 * phi / (4*pi^2)^(n-1);
end intrinsic;

intrinsic Coarea(B :: AlgQuat : Precision := DefaultPrecision, zK2 := 0) -> FldReElt
{
    The coarea of the Fuchsian group attached to a maximal order in B. The optional argument zK2 is the value at 2 of the Dedekind zeta function of the base field.
}
	R := RealField(Precision);
	pi := Pi(R);
	K := BaseField(B);
	ZK := MaximalOrder(K);
	DK := Discriminant(ZK);
    if zK2 eq 0 then
    	zK := LSeries(K : Precision := Precision);
	    zK2 := Evaluate(zK,2);
    end if;
	DB := RamifiedPlaces(B);
	if #DB ne 0 then
		phi := &*[Norm(p)-1 : p in DB];
	else
		phi := 1;
	end if;
	n := Degree(K);
	
	return Abs(R!DK)^(3/2) * zK2 * phi / (2^(2*n-3)*pi^(2*n-1));
end intrinsic;

intrinsic Psi(N :: RngOrdIdl) -> RngIntElt
{
    The multiplicative Psi function such that Psi(p^n) = Norm(p)^(n-1)*(Norm(p)+1).
}
facto := Factorization(N);
psi := 1;
for f in facto do
	np := Norm(f[1]);
	psi *:= np^(f[2]-1)*(np+1);
end for;
return psi;
end intrinsic;

function displacement(g,pr)
    B := Parent(g);
    vC := B`KlnV;
    d := Evaluate(Norm(g), vC : Precision := pr);
    t := Evaluate(Trace(g), vC : Precision := pr)/Sqrt(d);
    delta := Sqrt(t^2-4);
    a := (t+delta)/2;
    b := (t-delta)/2;
    return 2*Log(Max(Abs(a), Abs(b)));
end function;

intrinsic Displacement(g : Precision := DefaultPrecision) -> FldReElt
{
    The displacement of g acting on the hyperbolic 3-space.
}
    return displacement(g,Precision);
end intrinsic;
