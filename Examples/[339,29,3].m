load "../Code/BruteForcePoints.m";
load "../Code/Cascade.m";

B, C, n := Explode([339,29,3]);
K<s> := QuadraticField(-B);
OK := Integers(K);
CK , CKmap := ClassGroup(K);

O := FindOrder(B,C,K,OK);
picO, mO := PicardGroup(O);

print "The order is Z[sqrt(-339)]: ", O eq sub<OK|s>;
print "The class group of OK is Z/6Z: ",IsIsomorphic(CK, AbelianGroup([6]));
print "The class group of O is Z/3ZxZ/6Z: ",IsIsomorphic(picO, AbelianGroup([3,6]));

factorsC := Factorization(C*OK);
print "C*OK factors into two ideals: ", #factorsC eq 2;
J := factorsC[1][1];
print "J has order 2 in Cl(OK): ", Order((CKmap^(-1))(J)) eq 2;
print "J intersection O has order 6 in Cl(O): ", Order((mO^(-1))(J meet O)) eq 6;

print "Theorem A predicts no solutions: ", HasPointsMainThm(B,C,n) eq false;
print "We do not find points by brute force (up to ht=5000): ", #FindOnePointUpToHeight(B,C,n:height := 5000) eq 0; 