load "../Code/BruteForcePoints.m";
load "../Code/Cascade.m";

n := 3;
height := 1000;

function FindBCExample(r,rprime)
// The equations are x^2 + 32r · 83y^2 = 3r′· 23z^3
	return 3^(2*r)*83, 3^rprime*23;
end function;

B, C := FindBCExample(0,2);
print "(B,C) = (83,207): ", [B,C] eq [83,207];

print "There are no admissible twists A_(83,207): ", #AdmissibleTwists(B,C,n) eq 0;

print "There are twists A_(83,23): ", #AdmissibleTwists(83,23,n) ne 0;

bl := CascadeHasPoints(B,C,n);
print "The cascade finds points: ", bl;
print "We find points by brute force : ", #FindOnePointUpToHeight(B,C,n:height := height) ne 0; 