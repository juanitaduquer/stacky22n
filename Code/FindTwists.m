// Computes the sets of admissible twists A_{B,C}.

//FUNCTIONS

function FindSquareDecomposition(B)
/* returns B0 and f with B0 squarefree and B=f^2B0 */

	B0 := SquareFreeFactorization(B);
	f := Integers()!SquareRoot(B div B0);
	return B0, f;
end function;

function Is_nth_power(beta, n, R) 
//Checks whether beta is the n-th power of an ideal in R.  R must be a Dedekind domain.
  F := Factorization(beta*R);
  return &and[IsZero(factor[2] mod n) : factor in F];
end function;

function CheckDG(C, n, R) 
//Checks whether the case passes the Darmon-Graville global test.
  cGrp, m := ClassGroup(R);
  FF := Factorization(C*R);
  FactorizationC := Inverse(m)(FF[1][1]);
  Clmodn, quoMap := quo<cGrp | n>; //Doesn't work if class group is trivial
  if quoMap(FactorizationC) eq Identity(Clmodn) then
    return true;
  else return false;
  end if;
end function;

function CreateTuples(r)
// Creates tuples of length r with distinct entries in [0..r-1].
  ans := [[d-1: d in ElementToSequence(permutation)] : permutation in SymmetricGroup(r)];
  return ans;
end function;

function CreateTwists(n, units)
//Given n and the set of units, computes the set of representatives in units/units^n
  powers := CartesianPower([0..n-1],#units);
  twists := [];
  assert #units gt 0;

  twists := [&*[units[i]^pow[i]: i in [1..#pow]] : pow in powers];
  return twists;
end function;

function PrimeFactorsIdeal(I)
//Returns prime ideal divisors of an ideal I in a maximal order.
  return [pp[1] : pp in Factorization(I)];
end function;

function ValTestSplit(normList, primeList, OK, n) 
/*
d should belong to norm_n i.e. not be an n-th power itself,
Only for split rational primes. 
Output: list of d passing the split denominator test.*/
  d_list := [];
  for tup in normList, p in primeList do
    for P in Set(PrimeFactorsIdeal(p*OK)) meet Set(PrimeFactorsIdeal(tup[1]*OK)) do
      n1 := Valuation(tup[1]*OK, P) mod n;
      if n1 eq (n-1)/2 then
        n2 := Valuation(tup[1]*OK, Conjugate(P)) mod n;
        if n2 eq (n+1)/2 then
          d_list := Append(d_list, [tup[1], Norm(tup[1])]);
        end if;
      elif n1 eq (n+1)/2 then
        n2 := Valuation(tup[1]*OK, Conjugate(P)) mod n;
        if n2 eq (n-1)/2 then
          d_list := Append(d_list, [tup[1], Norm(tup[1])]);
        end if;
      end if;
    end for;
  end for;
  return d_list;
end function;

function ValTestRamified(normList, primeList, OK, n)
// Only for primes dividing GCD(B,C)
// Output: list of d passing the split denominator test.
  d_list := [];
  val_list := [];
  for tup in normList, p in primeList do
    for P in Set(PrimeFactorsIdeal(p*OK)) meet Set(PrimeFactorsIdeal(tup[1]*OK)) do
      n1 := Valuation(tup[1]*OK, P) mod n;
      d_list := Append(d_list, tup[1]);
      val_list := Append(val_list, n1);
    end for;
  end for;
  return d_list, val_list;
end function;

function CheckPrimesSplit(C,n,OK,twists,SSplitCPairs)
  // Returns the subset of twists that are admissible for PP|C split
  // SSplitCPairs gives the list of primes to check as <p,[PP, PPbar]>
  admissibleTwists := [];
  for d in twists do
    bad := false;
    for PPfact in SSplitCPairs do
      p := PPfact[1];
      PP := PPfact[2][1];
      PPbar := PPfact[2][2];
      vPP := Valuation(d*OK,PP);
      vPPbar := Valuation(d*OK,PPbar);
      vp := Valuation(C,p);
      if not ((vPP - vp*((n-1) div 2)) mod n eq 0 and (vPPbar - vp*((n+1) div 2)) mod n eq 0) 
        and not ((vPP - vp*((n+1) div 2)) mod n eq 0 and (vPPbar - vp*((n-1) div 2)) mod n eq 0) then
        bad := true;
        break;
      end if;
    end for;
    if not bad then
      Append(~admissibleTwists,d);
    end if;  
  end for;  
  return admissibleTwists;
end function;

function CheckPrimesNonSplit(n,primes,OK,twists : returnBool := false)
  // returns the subset of twists with v_PP(d) = 0 mod n for all PP in primes
  // If 
  admissibleTwists := [];
  for d in twists do
    bad := false;
    for PP in primes do
      vPP := Valuation(d*OK,PP);
      if not (vPP mod n eq 0) then
        bad := true;
        break;
      end if;
    end for;
    if not bad then
      if returnBool then
        return [true];
      else
        Append(~admissibleTwists,d);
      end if;  
    end if;  
  end for;  
  return admissibleTwists;
end function;

function FindOrder(B,C,K,OK)
// Defines the order contained in OK needed in the main theorems.
  B0, f := FindSquareDecomposition(B);
  s := K.1;
  if B0 mod 4 in [1,2] then
    O := sub<OK | f*s>;
  elif B0 mod 8 eq 3 and IsOdd(C) then
    O := sub<OK | f*s>;
  elif B0 mod 8 eq 3 and IsEven(C) then
    O := sub<OK | f*OK.2 >;
  elif B0 mod 8 eq 7 then
    O := sub<OK | f*OK.2>;
  end if;
  return O;
end function;

// New version of Magma fixes this V2.28-27
// function InversePicard(I,O,ClO,mapPic)
// // Computes the image of an ideal I of O in Pic(O)
//   assert GCD(Norm(I), Conductor(O)) eq 1;
//   for a in ClO do
//     if IsPrincipal(mapPic(a)*I) then
//       return -a;
//     end if;
//   end for;
//   error 2;
// end function;

function CheckInImage(B,C,n,K,OK,admissibleTwists)
// Now we check if the candidates belong to the image P(O,f)/nP(O,f)-> P(OK)/nP(OK)
  B0, f := FindSquareDecomposition(B);
  O := FindOrder(B,C,K,OK);
  picO, mapPic := PicardGroup(O);
  // CK, mapCl := ClassGroup(OK);
  invPic := Inverse(mapPic);
  nClO := sub<picO | [n*picO.i : i in [1 .. #Generators(picO)]]>;
  conductorO := Conductor(O);

  inImage := [];
  for d in admissibleTwists do 
    // coprime to f
    if GCD(Norm(d*OK), conductorO) eq 1 then
    // Check if in the image of P(O,f)/nP(O,f)-> P(OK)/nP(OK)
      if invPic(d*OK meet O) in nClO then
        Append(~inImage, d);
      end if;
    end if;
  end for;
  return inImage;    
end function;

function AdmissibleTwists(B, C, n)
/* Returns the set A_{B,C} of possible admissible twists */
  B0, f := FindSquareDecomposition(B);
  K<s> := QuadraticField(-B);
  OK := Integers(K);
  classGroup, clMap := ClassGroup(OK);
  toInvert := Set(&cat[[PP[1] : PP in Factorization(clMap(NN))] : NN in Generators(classGroup)] 
      cat [PP : PP in PrimeFactorsIdeal(2*n*C*OK)]); // TODO: invert f
  g := Numerator(C/GCD(B,C));

  assert #toInvert gt 0;
  idealToInvert := &*[ elt : elt in toInvert];
  SUG, uMap := SUnitGroup(idealToInvert);  
  S := [0..n-1];
  units := [uMap(gen) : gen in Generators(SUG)];
  twists := CreateTwists(n,units);
  unitNorms := [[t, Norm(t)] : t in twists];

  SSplitCPairs := [];
  for p in PrimeFactors(C) do
    if IsSplit(p,OK) then
      Append(~SSplitCPairs, <p,[elt[1]: elt in Factorization(p*OK)]>);
    end if;
  end for;

  admissibleTwistsSplit := CheckPrimesSplit(C,n,OK,twists,SSplitCPairs);

  //The primes in S-S_{C,Split}
  primes := [PP : PP in toInvert | Valuation(C*OK,PP) eq 0 or not IsSplit(PrimeDivisors(Norm(PP))[1],OK)];
  
  admissibleTwists := CheckPrimesNonSplit(n,primes, OK, admissibleTwistsSplit);  
  
  // Now we check if the candidates belong to the image P(O,f)/nP(O,f)-> P(OK)/nP(OK)
  admissibleTwists := CheckInImage(B,C,n,K,OK,admissibleTwists);

  return SetToSequence(Set(admissibleTwists));

  // norm_n := [];
  // both_n := [];
  // for tup in unitNorms do
  //   if is_nth_power(tup[2], n, O) then //would like to do this in the integers instead
  //     if is_nth_power(tup[1], n, O) then
  //       both_n := Append(both_n, tup);
  //     else
  //       norm_n := Append(norm_n,tup);
  //     end if;
  //   end if;
  // end for;

  // d_split := ValTestSplit(norm_n,PrimeFactorsIdeal(g),O,n);
  // // print "List of d with Nm(d) an nth power, which pass the (split) valuation test:";
  // // print d_split;

  // d_ram, val_ram := ValTestRamified(norm_n, PrimeFactorsIdeal(GCD(B,C)), O,n); //TODO: Check required!!! 

  // return d_split cat d_ram;
end function;


function AdmissibleTwistsTilde(B,C,n)
/* Returns the set tilde{A}_{B,C} of possible admissible twists
B0 = 7 mod 8 */

// TODO: add image condition. 
  B0 := Squarefree(B);
  assert B0 mod 8 eq 7;
  K<s> := QuadraticField(-B);
  OK := Integers(K);
  classGroup, clMap := ClassGroup(OK);
  toInvert := Set(&cat[[PP[1] : PP in Factorization(clMap(NN))] : NN in Generators(classGroup)] 
      cat [PP : PP in PrimeFactorsIdeal(2*n*C*O)]);
  g := Numerator(C/GCD(B,C));

  assert #toInvert gt 0;
  idealToInvert := &*[ elt : elt in toInvert];
  SUG, uMap := SUnitGroup(idealToInvert);  
  S := [0..n-1];
  units := [uMap(gen) : gen in Generators(SUG)];
  twists := Set(CreateTwists(n,units));
  unitNorms := [[t, Norm(t)] : t in twists];

  SSplitCPairs := [];
  for p in PrimeFactors(C) do
    // Only ckeck even primes, 2 will be at the end
    if IsOdd(p) and IsSplit(p,OK) then
      Append(~SSplitCPairs, <p,[elt[1]: elt in Factorization(p*OK)]>);
    end if;
  end for;

  admissibleTwistsSplit := CheckPrimesSplit(C,n,OK,twists,SSplitCPairs);

  //The primes in (S-S_{C,Split})-{PP2,PP2_bar}
  PP2, PP2bar := Explode(PrimeFactorsIdeal(2*OK));
  primes := [PP : PP in toInvert | (Valuation(C*OK,PP) eq 0 or not IsSplit(PrimeDivisors(Norm(PP))[1],OK)) and (not PP in [PP2,PP2bar])];
  
  admissibleTwistsNot2 := CheckPrimesNonSplit(n,primes, OK, admissibleTwistsSplit);  

  // Now we check 2.
  admissibleTwists := [];
  for d in admissibleTwistsNot2 do
    vP2 := Valuation(d*OK, PP2);
    vC2 := Valuation(C,2);
    vP2bar := Valuation(d*OK, PP2bar);
    if (vP2+vP2bar) mod n eq 0 then
      if (vP2 + (1+((n-1) div 2)*vC2)) mod n eq 0 or (vP2 - (1+((n-1) div 2)*vC2)) mod n eq 0 then
        Append(~admissibleTwists, d);
      end if;
    end if;    
  end for;

  // Now check that they are in the image P(O,f)/nP(O,f)-> P(OK)/nP(OK)
  admissibleTwists := CheckInImage(B,C,K,OK,admissibleTwists);
  return admissibleTwists;
end function;

