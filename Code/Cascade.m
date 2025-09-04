load "../Code/MainTheorem.m";

function ExcludedCase(B,C,n)
	// return true if the pair (B,C) belongs to the set E of excluded cases as defined in the paper.
	B0, f := FindSquareDecomposition(B);
	for p in PrimeDivisors(n) do
		vpf := Valuation(f,p);
		vpC := Valuation(C,p);
		if vpf gt vpC/2 then
			if IsEven(vpC) and vpf-vpC/2 ge n then
				return true;
			elif IsOdd(vpC) and vpf-vpC/2 ge (n+1)/2 then
				return true;
			end if;
		end if;
	end for;
	return false;
end function;

function CollectTp(infoTp,p,n)
// Runs through the filtration Y_{B,C}(Z)=union_r Y_{B,C}(Z;*_p^r)
// Collects list of B',C' for each r, as per section 6.2 of the paper (also conditions on y).
// This is, the list of B',C' whose points would imply a point in the original.

	B,C,rpow,M,pm, primes := Explode(infoTp);
	assert rpow eq 0;
	B0, f := FindSquareDecomposition(B);
	r := Valuation(f,p);
	assert r gt 0 and Valuation(C,p) eq 1;
	newPrimes := Append(primes,p);

	newList := [];
	if IsOdd(p) then
		rprime := Integers()!(Ceiling((2*r-1)/n)*n-2*r);
		// for t>r, there are no points.
		for t in [1..r] do
			if t ne 0 and t lt r and (2*t-1) mod n ne 0 then
				continue;
			elif t eq r and (2*t-1) mod n ne 0 then
				Append(~newList,<B div p^(2*r), C*p^rprime, 0, M, 1, newPrimes>);
			elif 0 lt t and t le r and (2*t-1) mod n eq 0 then
				Append(~newList,<B div p^(2*t), C div p, 0, p*M, 1, newPrimes>);
			// elif t eq 0 then
			// 	Append(~newList,[B, C, 0, M, 1]);
			end if;
		end for;
	
	else
		// Decompose on tilde* and tilde*^c
		// For tilde*
		for t in [1..r+1] do
			if t le r and (2*t-3) mod n ne 0 then
				continue;
			elif 1 lt t and t le r and (2*t-3) mod n eq 0 then
				Append(~newList,<Integers()!B*p^(-2*t+2), C div p, 0, 2*M, 1, newPrimes>);
			elif t eq r+1 and (2*t-3) mod n ne 0 then
				Append(~newList,<B div p^(2*r), Integers()!(C*p^(Ceiling((2*r-1)/n)*n-2*r)), 0, M, -1, newPrimes>);
			elif t eq r+1 and (2*t-3) mod n eq 0 then
				Append(~newList,<B div p^(2*r), C div p , 0, M,-1, newPrimes>);
			end if;
		end for;

		// For tilde*^c
		for t in [1..r+1] do
			if t lt r and (2*t-1) mod n ne 0 then
				continue;
			elif t lt r and (2*t-1) mod n eq 0 then
				Append(~newList,<B div p^(2*t), C div p, 0, 2*M, 1, newPrimes>);
			elif t eq r and (2*t-1) mod n ne 0 then
				Append(~newList,<B div p^(2*r), Integers()!(C*p^(Ceiling((2*r-1)/n)*n-2*r)), 0, M, 1, newPrimes>);
			elif t eq r and (2*t-1) mod n eq 0 then
				Append(~newList,<B div p^(2*r), C div p , 0, 2*M, 1, newPrimes>);
			end if;
		end for;
	end if;
	return newList;
end function;		

function Step1Cascade(B,C,n)
	// Compute P as in Step 1 of the cascade.
	// The format of elts of Tp is <B,C,r,M,+/-1,primes> such that:
			// the points are Y_{B,C}(Z;*_{p_i}^r,  M does not divide y), where
			// p_i ranges over primes (if the last entry is 1 and tilde(*) if -1).
	B0, f := FindSquareDecomposition(B);
	if GCD(f,C) eq 1 then
		pairsList := [<B,C,0,1,1,[p : p in PrimeDivisors(GCD(B,C))]>];
	else
		pairsList := [];
		for p in PrimeDivisors(GCD(f,C)) do
			if #pairsList eq 0 then
			// The first prime, initialize the information
				pairsList := [<B,C,0,1,1,[]>];
			end if;	
			for TpInfo in pairsList do
				pairsList := CollectTp(TpInfo,p,n);
			end for;
		end for;
	end if;
	return pairsList;
end function;


function IsStar0(f,C,primes);
	// Returns 1 if all the primes dividing f*C are already included
	// If not, returns the first prime.
	for p in PrimeDivisors(f*C) do
		if not p in primes then
			return p;
		end if;
	end for;
	return 1;		
end function;


function Step2Cascade(infoS,n)
// returns true if it finds a point in S.
// Otherwise, returns false, together with a prime p|GCD(f,C)
// (or none if no primes exist)
	B, C, r, M, pm, primes := Explode(infoS);
	B0, f := FindSquareDecomposition(B);
	star0 := IsStar0(f,C,primes) eq 1;

	// Apply the theorem for (B,C,n)
	bl := HasPointsMainThm(B,C,n);
	if bl then
		bl, twists := HasPointsMainThm(B,C,n);
		return true, twists;
	else
		if star0 then
			return false, [];
		else
			return false, [IsStar0(f,C,primes)];
		end if;
	end if;		
end function;

function Step3Cascade(infoS,n,p)
// Runs Step 3 of the cascade
	B, C, rpow, M, pm, primes := Explode(infoS);
	assert rpow eq 0;

	B0,f := FindSquareDecomposition(B);

	newList := [];

	newPrimes := Append(primes,p);
	if f mod p eq 0 then
		r := Valuation(f,p);
		if IsOdd(p) then 
		// Lemma 6.2
			for t in [1..r] do
				if t lt r and t mod n ne 0 then
					continue;
				elif t le r and t mod n eq 0 then
					Append(~newList,< B div p^(2*t), C, 0, p*M, 1, newPrimes>);
				elif t eq r and n mod t ne 0 then
					Append(~newList,< B div p^(2*t), C*p^(Ceiling(2*r/n)*n-2*r), 0, M, 1, newPrimes>);
				end if;
			end for;
		elif IsEven(p) then
		// Lemma 6.3 and use tildestar and its complement
			for t in [1..r+1] do
				if 0 lt r and t le r then
					continue;
				elif t eq r+1 and t-1 mod n ne 0 then
					Append(~newList,< B div p^(2*t), Integers()!(C*p^(Ceiling(2*r/n)*n-2*r)), 0, M, -1, newPrimes>);
				end if;
			end for;

			// Complement
			for t in [1..r+1] do
				if 0 lt r and t lt r and t mod n ne 0 then
					continue;
				elif t le r and t mod n ne 0 then
					Append(~newList,< B div p^(2*t), C, 0, p*M, 1, newPrimes>);
				elif t eq r and n mod t ne 0 then
					Append(~newList,< B div p^(2*t), Integers()!(C*p^(Ceiling(2*r/n)*n-2*r)), 0, M, 1, newPrimes>);
				end if;
			end for;
		end if;
	elif C mod p eq 0 then
		r := Floor(Valuation(C,p)/2);
		if IsOdd(p) then
		// Lemma 6.6.
			for t in [1..r] do
				Append(~newList,< B, C div p^(2*t), 0, M, 1, newPrimes>); //The condition on z is covered by MainThm
			end for;	
		else 
		// Lemma 6.7
			assert f mod p ne 0;
			for t in [1..r] do
				Append(~newList,< B, C div p^(2*(t-1)), 0, M, 1, newPrimes>); //The condition on z is covered by MainThm
				Append(~newList,< B, C div p^(2*t), 0, M, 1, newPrimes>);
			end for;
		end if;		
	end if;		

	return newList;
end function;

function CascadeHasPoints(B,C,n)
	/* Runs through our cascade to proof that there are no integer points
			on x^2 + By^2 = Cz^3
			Returns true if there is a point (together with a certificate)
			False if there are no points
			error if (B,C) is in the excluded set
	*/

	print "Running the cascade for (B,C)=",B,C;
	if ExcludedCase(B,C,n) then
		print "This is an excluded case";
		assert false;
	end if;	

	// Step 0
	g := GCD(B,C);
	_, sq := SquareFreeFactorization(g);
	if sq gt 1 then
		B := B div sq^2;
		C := C div sq^2;
		g := GCD(B,C);
		assert IsSquarefree(g);
		print "Step 0 changes (B,C) to (B',C') = (", B,",",C,").";
	end if;

	// Now pairsList is as in the end of Step 1.
	pairsList := Step1Cascade(B,C,n);

	print "The list after Step 1 is ", pairsList;

	// The format of elts of pairsList is <B,C,r,M,+/-1,primes> such that:
	// the points are Y_{B,C}(Z;*_{p_i}^r,  M does not divide y), where
	// p_i ranges over primes (if the last entry is 1 and tilde(*) if -1).

	// Iterate Step 2
	while #pairsList ne 0 do
		SInfo := pairsList[1];
		print "We are looking at SInfo and running Step 2", SInfo;
		bl, primeOrTwist := Step2Cascade(SInfo,n);
		if bl then
		// We have found points and stop!
			print "We found a point using our main theorem";
			return true, primeOrTwist;
		else
			if #primeOrTwist eq 0 then
			// There are no points and we remove S
				Remove(~pairsList,1);
			else
			// We add all of the possible star_p^t to PP using Step 3
				p := primeOrTwist[1];
				Remove(~pairsList,1);
				pairsList cat:= Step3Cascade(SInfo,n,p);
				print "In Step 3, we used p = ", p, "To get the new list", pairsList;
			end if;	
		end if;
	end while;
	print "Provably, there are no points";
	return false;
end function;	



/*

	if g eq 1 then
		primes := PrimeFactors(g);
		for p in primes do
			r := Valuation(f,p);
			if IsEven(p) then
				
	else
		// Construct the set T_{p_1}
		primesG := PrimeDivisors(g);
	end if;

	B0, f := FindDecomposition(B);

	K := QuadraticField(-B0);
	OK := Integers(K);
	g := GCD(f,C);

	primesC := PrimeFactors(C);


	if g eq 1 and (B0-7) mod 8 eq 0 and IsOdd(C) then
		inertC := [p : p in primesC | IsInert(p*OK)];
		if #inertC eq 0 or &and[IsEven(Valuation(C,p)) : p in inertC] then
			twists := AdmissibleTwists(B,C,n);
			if #twists ne 0 then
			// No points
			
			end if;
		end if;
	elif g eq 1 and (B0-7) mod 8 eq 0 and IsEven(C) then
		// No points
	elif g eq 1 and (B0-7) mod 8 eq 0 then
		inertC := [p : p in primesC | IsInert(p*OK)];
		if #inertC eq 0 or &and[IsEven(Valuation(C,p)) : p in inertC] then
			twists := AdmissibleTwists(B,C,n);
			if #twists ne 0 then
			// No points
			
			end if;
		end if;	
	end if;	

	*/