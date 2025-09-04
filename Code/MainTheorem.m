/*
This applies the main theorem for points where f and C are relatively prime
*/

load "../Code/FindTwists.m";

function HasPointsMainThm(B,C,n)
/* Given integers B and C and an odd positive integer n,
	it applies the main theorem and retuns false if 
	Y_{B,C}(Z) = empty, together with a certificate of a prime
	if possible, or nothing if there are simply no twists.
	If Y_{B,C}(Z) is nonempty, it returns true, together with a 
	list of twists with points.
*/

	B0 := SquareFreeFactorization(B);
	f := Integers()!SquareRoot(B div B0);

	assert B eq B0*f^2;

	if GCD(f,C) ne 1 then
		print "GCD(f,C)!=1";
		assert false;
	end if;

	K<s> := QuadraticField(-B0);
	OK := Integers(K);

	if B0 mod 4 in [1,2] or (B0 mod 4 eq 3 and IsOdd(C)) then
		for p in PrimeFactors(C) do 
			if IsSplit(p,OK) then
				continue;
			elif IsInert(p,OK) then
				return false, p;
			else
				if p^2 in Divisors(C) then
					return false, p;
				else
					continue;
				end if;
			end if;
		end for;

		 
		listTwists := AdmissibleTwists(B,C,n); 
		if #listTwists ne 0 then
			return true, listTwists;
		end if;
		return false, -1;

	elif B0 mod 4 eq 3 then
		if Valuation(C,2) ne 2 then
			return false, 2;
		end if;

		for p in PrimeFactors(C) do 
			if IsEven(p) then
				if B0 mod 8 eq 3 and Valuation(C,2) ne 2 then
					return false, 2;
				end if;	
			elif IsSplit(p,OK) then
				continue;
			elif IsInert(p,OK) then
				return false, p;
			else
				if p^2 in Divisors(C) then
					return false, p;
				else
					continue;
				end if;
			end if;
		end for;
				
		listTwists := AdmissibleTwistsTilde(B,C,n);
		if #listTwists ne 0 then
			return true, listTwists;
		end if;
		return false, -1;
	end if;	
end function;	
