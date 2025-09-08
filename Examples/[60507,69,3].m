load "../Code/BruteForcePoints.m";
load "../Code/Cascade.m";

n := 3;
height := 10000;

function FindBCExample(r,rprime)
// The equations are x^2 + 32r · 83y^2 = 3r′· 23z^3
	return 3^(2*r)*83, 3^rprime*23;
end function;

B, C := FindBCExample(3,1);
print "(B,C) = (60507,69): ", [B,C] eq [60507,69];

print "Excluded case: ", ExcludedCase(B,C,n);

print "All points on Y_(60507,69)(Z) up to height 5000 have 3|y:", &and[P[2] mod 3 eq 0: P in FindPointsUpToHeight(B,C,n : height:=height)];


