load "../Code/BruteForcePoints.m";
load "../Code/Cascade.m";

n := 3;
height := 1000;

function FindBCExample(r,rprime)
// The equations are x^2 + 32r · 83y^2 = 3r′· 23z^3
	return 3^(2*r)*83, 3^rprime*23;
end function;

B, C := FindBCExample(4,1);
print "(B,C) = (544563,69): ", [B,C] eq [544563,69];

print "Excluded case: ", ExcludedCase(B,C,n);

print "There is a point on Y_(6723,23)(Z;*_3^0,3 nmid y) :", FindOnePointUpToHeight(B,C,n : height:=height)[1][2] mod 3 ne 0;