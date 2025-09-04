/* The local test implemented in the local solubility section in the paper */

function LocalTestAtp(B,C,n,p) 
// Returns true if x^2+By^2=Cz^n has a point over F_p.

  // check l even or odd
  l := Valuation(C,p);
  if l mod 2 eq 0 then
    return true;
  end if;

  // assume l odd
  k := Valuation(B,p);
  
  // k odd
  if k mod 2 eq 1 then
    if l lt k and k lt n+l then
      return false;
    else
      return true;
    end if;
  end if;  
  
  // l odd and k even    
  if p eq 2 then
    if k le l - 1 and (B div 2^k) mod 8 eq 3 then
      return false;
    elif l-1 lt k and k lt n+l-2 and (B div 2^k) mod 8 ne 7 then
      return false;
    elif k eq (n+l-2) and (B div 2^k) mod 4 eq 1 then
      return false;
    else
      return true;
    end if;  
  else
    B0 := (B div p^k);
    if k lt n+l and LegendreSymbol(-B0,p) eq -1 then
      return false;
    else
      return true;
    end if;
  end if;
end function;  
    
function LocalTest(B,C,n)
// Returns true if x^2+By^2=Cz^n has a point over F_p for all p.
  if C eq 1 then
    return true;
  else  
    return &and[LocalTestAtp(B,C,n,p) : p in PrimeDivisors(C)];
  end if;  
end function;  
