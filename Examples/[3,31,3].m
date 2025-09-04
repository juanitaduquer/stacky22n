load "../Code/BruteForcePoints.m";
load "../Code/Cascade.m";

B, C, n := Explode([3,31,3]);
K<s> := QuadraticField(-B);
OK := Integers(K);
O := FindOrder(B,C,K,OK);
CL := ClassGroup(OK);

print "OK equals O: ", OK eq O;
print "Class group is trivial: ", #CL eq 1;

factorsC := Factorization(C*OK);
print "C*OK factors into two ideals: ", #factorsC eq 2;

J := factorsC[1][1];
JO := J meet O;

O3 := sub<O|3*O.2>;
print "The ideals are contained in an order of conductor 3: ",JO meet O3 eq JO;

print "All points on Y_(B,C)(Z) up to height 5000 have 3|y:", &and[P[2] mod 3 eq 0: P in FindPointsUpToHeight(B,C,n : height:=5000)];