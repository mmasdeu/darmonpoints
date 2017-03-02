/*

enumeration.m
procedures for enumerating elements of arithmetic Kleinian groups

enumeration.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../kleinian.m" : isscalar, dgm;
import "normalizedbasis.m" : CheckTimeOut;

/*
    INPUT
    O : an order in a quaternion algebra
    Lat : a reference for storing the result lattice
    TZB : a reference for storing the Z-basis
    nzb : a reference for storing the cardinality of the basis
    pr : the precision
    factor : a scaling factor for the quadratic form

    OPTIONAL
    Center1, Center2 : the centers of the quadratic form

    Initializes the lattice obtained by O equipped with the positive definite quadratic form with centers Center1, Center2.
*/
procedure InitializeLattice(O, ~Lat, ~TZB, ~nzb, pr, factor, ~HGM, ~basismat : Center1 := 0, Center2 := 0, Balance := 1)
    if HGM eq 0 then
        HGM,ZB,basismat := dgm(O : Precision := pr, Facteur := 4*factor, Center1 := Center1, Center2 := Center2, Balance := Balance, ComputeHGM := true, Matrices := basismat);
    end if;
    DGM,ZB,basismat := dgm(O : Precision := pr, Facteur := 4*factor, Center1 := Center1, Center2 := Center2, Balance := 0, HGM := HGM, Matrices := basismat);
    ispd := IsPositiveDefinite(DGM);
    if not ispd then 
        vprint Kleinian, 2 :"\nTHE QUADRATIC FORM IS NOT POSITIVE DEFINITE !!!";
        TZB := [];
        return;
    end if;

    nzb := #ZB;
    Gram2,T := LLLGram(DGM : Fast := 1, Proof := false);
    TZB := [ &+[T[i,k]*ZB[k] : k in [1..nzb]] : i in [1..nzb]];

    Lat := LatticeWithGram(Gram2);
end procedure;

/*
    INPUT
    x : the element of order to be processed
    order : an order in a quaternion algebra
    ZK : the base ring of order
    Enum : a reference for storing the elements of the group
    partialgpelt : a reference to a counter
    grouptype : an integer specifying which group is considered : 1 = norm one, 2 = units, 3 = normalizer
    bp : a bound on the primes to be stored
    primes : a reference for storing the elements whose norm generates a prime ideal
    maxp : a reference to a counter
    allowsq : a boolean specifying whether units with square norm should be accepted
    fuchsian : a boolean specifying whether the group is a Fuchsian group

    Stores x (maybe scaled) in the relevant container
*/
procedure ProcessVector(x, order, ZK, ~Enum, ~partialgpelt, grouptype, bp, ~primes, ~maxp, allowsq, fuchsian)
//CheckTimeOut();
    nx := Norm(x);
    if isscalar(x) or nx eq 0 then
        return;
    end if;
    if Abs(NormAbs(nx)) eq 1 then
        if (nx eq 1 or (IsSquare(nx) and allowsq)) then
            x := x/Sqrt(nx);
            if x in order and not x in Enum and (not fuchsian or IsTotallyPositive(nx)) then
                Include(~Enum, x);
                partialgpelt +:= 1;
            end if;
        elif allowsq and grouptype ge 2 /*Units or Maximal*/ and (not fuchsian or IsTotallyPositive(nx)) then
            Include(~Enum, x);
        end if;
    else
        if grouptype eq 3 and order^x eq order and (not fuchsian or IsTotallyPositive(nx)) then
            Include(~Enum, x);
        end if;
        if Abs(NormAbs(nx)) le bp and IsPrime(nx*ZK) and (not fuchsian or IsTotallyPositive(nx)) then
            inprimes := false;
            ip := 1;
            while not inprimes and ip le maxp do
                p := primes[ip];
                if Norm(p)*ZK eq nx*ZK then
                    inprimes := true;
                end if;
                ip := ip+1;
            end while;
            if not inprimes then
                Append(~primes,x);
                maxp := maxp+1;
            end if;
        end if;
    end if;
end procedure;

/*
    INPUT
    Enum : a reference for storing the enumerated group elements
    u : a reference for the bound on the quadratic form
    ZB : the Z-basis of order corresponding to the lattice Lat
    nzb : the cardinality of ZB
    Lat : a reference to the lattice in which the enumeration should be performed
    totalvect : a reference to a counter
    totalgpelt : a reference to a counter
    NbEnum : the desired number of group elements
    stepu : a reference to the increment on the bound on the quadratic form
    order : the order containing the relevant group
    factor : the scaling factor of the quadratic form
    primes : a reference for storing elements whose norm generates a prime ideal
    ZK : the base ring of order
    bp : a bound on the primes to be stored
    grouptype : an integer specifying which group is considered : 1 = norm one, 2 = units, 3 = normalizer
    allowsq : a boolean specifying whether units with square norm should be accepted
    divadapt : a reference to a counter to automatically adapt the value of stepu
    fuchsian : a boolean specifying whether the group is a Fuchsian group
    randomized : a boolean specifying whether the enumeration is randomized at finite places

    Enumerates elements of the group corresponding to small vectors in Lat
*/
procedure Enumerate(~Enum,~u,ZB,nzb,~Lat,~totalvect,~totalgpelt, NbEnum, ~stepu, order, factor, ~primes, ZK, bp, grouptype, allowsq, ~divadapt, fuchsian, randomized)
    maxp := #primes;
	partialvect := 0;
	partialgpelt := 0;
    if NbEnum eq 0 then
        maxvenum := 1000;
    else
        maxvenum := 10000;
    end if;
	t := Cputime();
	nbproc := 0;
    repeat
		if u eq 0 then
            P := ShortVectors(Lat,stepu : Prune := [Max(0.5,(nzb-i)/nzb*1.) : i in [1..nzb]], Max := maxvenum+2);
		else
			P := ShortVectorsProcess(Lat,u,u+stepu);
		end if;
		nbproc +:= 1;
		u +:= stepu;
        if nbproc gt 1 then vprintf Kleinian, 2: "*"; end if;
		nm := 0;
        j := 1;
		while (Type(P) ne SeqEnum or j le #P) and nm ne -1 and (NbEnum ne 0 or partialvect lt maxvenum) and (NbEnum ge 1 or partialgpelt lt 11) do
            if Type(P) eq SeqEnum then
			    v,nm := Explode(P[j]);
            else
                v,nm := NextVector(P);
            end if;
            j +:= 1;
			x := &+[Round(v[i])*ZB[i] : i in [1..nzb]];
			partialvect +:= 1;
            ProcessVector(x, order, ZK, ~Enum, ~partialgpelt, grouptype, bp, ~primes, ~maxp, allowsq, fuchsian);
            if partialvect mod 1000 eq 0 then vprintf Kleinian, 2: "."; end if;
            if partialvect mod 10000 eq 0 then vprintf Kleinian, 3: "%o", partialgpelt; end if;
		end while;
    until partialgpelt ge NbEnum;

if NbEnum le 1 and not randomized then
    if partialvect ge 900 then
        stepu /:= (100+5/divadapt)/100;
    end if;
    if partialvect ge 200 then
        stepu /:= (100+2/divadapt)/100;
    end if;
    if partialvect ge 60 then
        stepu /:= (100+1/divadapt)/100;
    end if;
    if partialvect le 1 then
        stepu *:= (100+7/divadapt)/100;
    end if;
    if partialvect le 10 then
        stepu *:= (100+4/divadapt)/100;
    end if;
    if partialvect le 20 then
        stepu *:= (100+1/divadapt)/100;
    end if;
    divadapt +:= 1/9;
end if;

	totalvect +:= partialvect;
	totalgpelt +:= partialgpelt;
    vprintf Kleinian, 3: "(%o)", partialvect;
    if partialgpelt gt 0 then vprintf Kleinian, 2: "[+%o] ", partialgpelt; end if;
    vprintf Kleinian, 3: "stepu = %o\n", RealField(5)!stepu;
end procedure;
