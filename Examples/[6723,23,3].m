load "../Code/BruteForcePoints.m";
load "../Code/Cascade.m";

n := 3;
height := 1000;

function FindBCExample(r,rprime)
// The equations are x^2 + 32r · 83y^2 = 3r′· 23z^3
	return 3^(2*r)*83, 3^rprime*23;
end function;

B, C := FindBCExample(2,0);
print "(B,C) = (6723,23): ", [B,C] eq [6723,23];

// Preliminaries

// Check if there are points
points := FindPointsUpToHeight(B,C,n : height := height); 
if #points eq 0 then
  print "No primitive solution of height up to", height;
else 	
	print "This equation has ", #points, " solutions of height up to", height;
end if;

// Class groups
B0, f := FindSquareDecomposition(B);
K<s> := QuadraticField(-B0);
OK := Integers(K);
CK, phi := ClassGroup(OK);
O := FindOrder(B,C,K,OK);
CO, phiO := PicardGroup(O);

print "The class group of O is Z/3Z x Z/18Z: ", IsIsomorphic(CO,AbelianGroup([3,18]));
// Factorization of C
factorsC := Factorization(C*OK);
print "C factors as a product of two ideals: ", #factorsC eq 2;
J := factorsC[1][1];
print "The factors of C (J and J') are principal: ", IsPrincipal(factorsC[1][1]) and IsPrincipal(factorsC[2][1]);
JO := J meet O;
print "J intersected with O is in (0,3): ", (phiO^(-1))(JO) eq 3*CO.2;

// print "The admissible twists are";
admissibleTwists := AdmissibleTwists(B, C, n);
// admissibleTwists;

print "There are 6 admissible twists: ", #admissibleTwists eq 6;

print "We find points by brute force : ", #FindOnePointUpToHeight(B,C,n:height := height) ne 0; 

