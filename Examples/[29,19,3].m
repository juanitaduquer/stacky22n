load "../Code/BruteForcePoints.m";
load "../Code/Cascade.m";

B, C, n := Explode([29,19,3]);
K<s> := QuadraticField(-B);
OK := Integers(K);

AT :=  [418  - 19*s,
    -418  + 19 *s,
    3059  - 1140 *s,
    -3059  + 1140 *s,
    3610  + 1083 *s,
    -3610  - 1083 *s,
    159182  + 17575 *s,
    -159182  - 17575 *s,
    164255  - 15884 *s,
    -164255  + 15884 *s,
    650522  - 534641 *s,
    -650522  + 534641 *s];

print "There admissible twists we list are correct: ", Set(AdmissibleTwists(B,C,n)) eq Set(AT);
print "We find points by brute force (up to ht=5000): ", #FindOnePointUpToHeight(B,C,n:height := 5000) ne 0; 