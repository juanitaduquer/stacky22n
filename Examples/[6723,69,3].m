load "../Code/BruteForcePoints.m";
load "../Code/Cascade.m";

n := 3;
height := 1000;

function FindBCExample(r,rprime)
// The equations are x^2 + 32r · 83y^2 = 3r′· 23z^3
	return 3^(2*r)*83, 3^rprime*23;
end function;

B, C := FindBCExample(2,1);
print "(B,C) = (6723,69): ", [B,C] eq [6723,69];

bl := CascadeHasPoints(B,C,n);
print "The cascade finds points: ", bl;
print "We find points by brute force : ", #FindOnePointUpToHeight(B,C,n:height := height) ne 0; 