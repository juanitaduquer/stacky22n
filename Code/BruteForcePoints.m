//To find points by brute force on x^2 + By^2 = Cz^3;
//Finds points of bounded Height

function IsPrimitiveSolution(x,y,z)
// Decides if the solution (x,y,z) is primitive.
	return GCD(GCD(x,y),z) eq 1;
end function;

function FindPointsUpToHeight(B,C,n:height := 5000)
// Returns points on x^2 + By^2 = Cz^3 with x,y,z <= height
	solutions := [];
	for x0,y0 in [1..height] do
		test:= (1/C)*(x0^2 + B*y0^2);
		if Denominator(test) eq 1 then //conditions on test being an integer to increase speed. If test isn't an integer, its n-th root has no chance of being one.
			test := Numerator(test);
			truth_val, z0 := IsPower(test, n); //truth_val, z:= IsPower(8,3) returns true 2; if truth_val eq false, then z is not assigned.
			if truth_val then
				if IsPrimitiveSolution(x0,y0,Numerator(z0)) then
					// print "This equation has a primitive solution with height less than", height;
					// print "Solution: (", x0, ",", y0, ",", z0, ")"; 
					Append(~solutions, [x0,y0,z0]);
				end if;
			end if;
		end if;
	end for;
	return solutions;
end function;

function FindOnePointUpToHeight(B,C,n:height := 5000)
// Returns points on x^2 + By^2 = Cz^3 with x,y,z <= height
	solutions := [];
	for x0,y0 in [1..height] do
		test:= (1/C)*(x0^2 + B*y0^2);
		if Denominator(test) eq 1 then //conditions on test being an integer to increase speed. If test isn't an integer, its n-th root has no chance of being one.
			test := Numerator(test);
			truth_val, z0 := IsPower(test, n); //truth_val, z:= IsPower(8,3) returns true 2; if truth_val eq false, then z is not assigned.
			if truth_val then
				if IsPrimitiveSolution(x0,y0,Numerator(z0)) then
					// print "This equation has a primitive solution with height less than", height;
					// print "Solution: (", x0, ",", y0, ",", z0, ")"; 
					return [[x0,y0,z0]];
				end if;
			end if;
		end if;
	end for;
	return [];
end function;

function BoolPointsUpToHeight(B,C,n : height := 5000)
	// True if it finds a point on x^2 + By^2 = Cz^3; (with the point as certificate)
	// The point satisfies x0,y0<hts
	// False if no points exist.

	solutions := [];
	for x0,y0 in [1..height] do
		test := (1/C)*(x0^2 + B*y0^2);
		if Denominator(test) eq 1 then //conditions on test being an integer to increase speed. If test isn't an integer, its n-th root has no chance of being one.
			test := Numerator(test);
			truth_val, z0 := IsPower(test, n); //truth_val, z:= IsPower(8,3) returns true 2; if truth_val eq false, then z is not assigned.
			if truth_val then
				if IsPrimitiveSolution(x0,y0,Numerator(z0)) then
					// print "This equation has a primitive solution with height less than", height;
					// print "Solution: (", x0, ",", y0, ",", z0, ")"; 
					return true, [x0,y0,z0];
				end if;
			end if;
		end if;
	end for;
	return false, _;
end function;