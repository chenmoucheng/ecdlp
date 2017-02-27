/* Montgomery */

assert q ne 2;
if IsPrime(n) then assert l eq 1; end if;

 E := AssociativeArray();
 E["form"] := "Montgomery"; E["form"];
 repeat
 	repeat
 		A := Random(k);
 		B := Random(k);
 	until B*(A^2-4) ne 0;
 	E["curve"] := EllipticCurve([(3-A^2)/(3*B^2), (2*A^3-9*A)/(27*B^3)]);
 	Q := Random(E["curve"](k));
 	p := fs[#fs][1] where fs is Factorization(Order(Q));
 until p ge q^(n - 4);
 E["curve"]; Coefficients(E["curve"]);
 cofactor := Integers()!(Order(Q)/p);
 P := cofactor*Q;
 print "Base point:",P; print "Order:",Order(P); assert IsPrime(Order(P));

 // V: l-dimensional linear subspace of k over K that determines factor base FB
 WeitoMon := function(Q)
 	u := Q[1]/Q[3];
 	v := Q[2]/Q[3];
 	x := B*u-1/3*A;
 	y := B*v;
 	return [x, y];
 end function;

 // V: l-dimensional linear subspace of k over K that determines factor base FB
 // FB is on Weierstrass, but V is on Montgomery
 E["FBtoV"] := function(Q)
   return WeitoMon(Q)[1];
 end function;


// V is constructed on Montgomery curve
E["VtoFB"] := function(t)
  R<X,Y> := PolynomialRing(k,2);
  Z := Roots(Evaluate(f,[t,R.1]))
    where f is -B*Y^2+X^3+A*X^2+X
    where R is PolynomialRing(k);
  return [E["curve"]![t/B + A/(3*B),z[1]/B] : z in Z];
end function;

// return numerator after reduction to common denominator
RewriteT2ESP := function(Vars,i)
  R := Universe(Vars);
  S := PolynomialRing(PolynomialRing(R),#Vars);
  map := hom<S->R|[Vars[j]^2+1 : j in [1..m]]>;
  Term := Terms(ElementarySymmetricPolynomial(S, i));
  if i eq #Vars then
    return map(Term)[1];
  else
    Poly :=  R ! 0;
    for j in Term do
      Diff := {S.i : i in [1..#Vars]} diff SequenceToSet([Factorization(j)[l][1] : l in[1..i] ]);
      Poly +:= map(j) * &*hom<S->R|Vars>(SetToSequence(Diff));
    end for;
  end if;
  return Poly;
end function;


E["Iauxiliary"] := Ideal({RewriteESP(t,m)*s[i] - RewriteT2ESP(t,i) : i in [1..m]});
E["Jcondition"] := Ideal(&cat[T[i][(l + 1)..n] cat S[i][(i*(l - 1) + 2)..n] : i in [1..m]]);

// Semaev's summation polynomial

E["f3"] := function(x0,x1,x2)
  return x0^2*x1^2 - 2*x0^2*x1*x2 + x0^2*x2^2 - 2*x0*x1^2*x2 - 2*x0*x1*x2^2 - 4*x0*x1*x2*A - 2*x0*x1 - 2*x0*x2 + x1^2*x2^2 - 2*x1*x2 + 1;
end function;
