load "../Code/BruteForcePoints.m";
load "../Code/Cascade.m";

n := 3;
height := 1000;

function FindBCExample(r,rprime)
// The equations are x^2 + 32r · 83y^2 = 3r′· 23z^3
	return 3^(2*r)*83, 3^rprime*23;
end function;

// The first example with coprimes
B, C := FindBCExample(0,0);
print "(B,C) = (83,23): ", [B,C] eq [83,23];

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

print "The class group of O is Z/9Z: ", IsIsomorphic(CO,AbelianGroup(9));
// Factorization of C
factorsC := Factorization(C*OK);
print "C factors as a product of two ideals: ", #factorsC eq 2;
J := factorsC[1][1];
print "The factors of C (J and J') are principal: ", IsPrincipal(factorsC[1][1]) and IsPrincipal(factorsC[2][1]);
JO := J meet O;
print "J intersected with O is not principal: ", IsPrincipal(JO) eq false;
print "The order of J intersected with O in Pic(O) is 3: ", IsPrincipal(JO^3) and not IsPrincipal(JO^2);

// print "The admissible twists are";
admissibleTwists := AdmissibleTwists(B, C, n);
// admissibleTwists;

print "There are 18 admissible twists: ", #admissibleTwists eq 18;

/*


// Example: (B,C,n) = (3^8*83, 3*23, 3)

B := 3^8*83;
C := 3*23;
// has solutions, all with 3 not dividing y

// two cascade targets: 
B := 83;
C := 3*23;
// no solutions
B := 3^4*83;
C := 23;
// has solutions, all with 3 not dividing y



// Example: (3^6*83, 3*23, 3)

B := 3^6*83;
C := 3*23;
// no solutions

// two cascade targets: 
B := 3^2*83; // t = 2
C := 23;
// no solutions

B := 83; // t = 3
C := 3*23;
// no solutions


// Example: (3^4*83, 23, 3)

B := 3^4*83;
C := 23;
Of := Order([1, 9*a]);
COf, phiOf := PicardGroup(Of);
COf;
Abelian Group isomorphic to Z/3 + Z/18
Defined on 2 generators
Relations:
    3*COf.1 = 0
    18*COf.2 = 0
JOf := J meet Of;
for k in [1..9] do
    <k, IsPrincipal(JOf^k)>;
    end for;
// JOf has order 6 in COf
psiOf := Inverse(phiOf);
psiOf(JOf);
// JOf is a cube in COf, so class gp obstruction vanishes


// Example: (3^2*83, 23, 3)

B := 3^2*83;
C := 23;
Of := Order([1, 3*a]);
COf, phiOf := PicardGroup(Of);
COf;
Abelian Group isomorphic to Z/9
Defined on 1 generator
Relations:
    9*CO.1 = 0
JOf := J meet Of;
for k in [1..9] do
    <k, IsPrincipal(JOf^k)>;
    end for;
// JOf has order 6 in COf
psiOf := Inverse(phiOf);
psiOf(JOf);
// JOf is a cube in COf, so class gp obstruction vanishes


// Example: (3^4*83, 3*23, 3)

B := 3^4*83;
C := 3*23;
// one cascade target: // t = 2
B := 83;
C := 23;
// done by base case





*/