/*  Montgomery */

assert q ne 2;

E := AssociativeArray();
E["form"] := "Montgomery"; E["form"];
repeat
	repeat
		A := Random(k);
		B := Random(k);
	until B*(A^2-4) ne 0;
	E["curve"] := EllipticCurve([(3-A^2)/(3*B^2), (2*A^3-9*A)/(27*B^3)]);
	Q := Random(E["curve"](k));
  cofactor := Integers()!(Order(Q)/fs[#fs][1]) where fs is Factorization(Order(Q));
until cofactor lt 16;
E["curve"]; Coefficients(E["curve"]);
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

E["Iauxiliary"] := Ideal({s[i] - RewriteESP(t,i) : i in [1..m]});
E["Jcondition"] := Ideal(&cat[T[i][(l + 1)..n] cat S[i][(i*(l - 1) + 2)..n] : i in [1..m]]);

// Semaev's summation polynomial

E["f3"] := function(x0,x1,x2)
  return x0^2*x1^2 - 2*x0^2*x1*x2 + x0^2*x2^2 - 2*x0*x1^2*x2 - 2*x0*x1*x2^2 - 4*x0*x1*x2*A - 2*x0*x1 - 2*x0*x2 + x1^2*x2^2 - 2*x1*x2 + 1;
end function;
