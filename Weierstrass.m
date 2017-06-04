/*
 * Weierstrass curves
 */

E := AssociativeArray();
E["form"] := "Weierstrass"; E["form"];
cofactor := q eq 2 select 2 else 1;
repeat
  repeat
    E["curve"] := q eq 2 select EllipticCurve([1,1,0,0,Random(k)]) else EllipticCurve([Random(k),Random(k)]);
  until Discriminant(E["curve"]) ne 0;
  order := Order(E["curve"](k));
until IsDivisibleBy(order,cofactor) and IsPrime(Integers()!(order/cofactor));
P := cofactor*Random(E["curve"](k));
E["curve"]; Coefficients(E["curve"]);
print "jInvariant:",jInvariant(E["curve"]);
print "Base point:",P; print "Order:",Order(P); assert IsPrime(Order(P));

// V: l-dimensional linear subspace of k over K that determines factor base FB

E["FBtoV"] := function(Q)
  assert Q ne E["curve"]!0;
  return Q[1]/Q[3];
end function;

E["VtoFB"] := function(t)
  Z := Roots(Evaluate(f,[t,R.1,1]))
    where f is DefiningPolynomial(E["curve"])
    where R is PolynomialRing(k);
  return [E["curve"]![t,z[1]] : z in Z];
end function;

E["Iauxiliary"] := Ideal({s[i] - RewriteESP(t,i) : i in [1..m]}); Groebner(E["Iauxiliary"]);
E["Jcondition"] := Ideal(&cat[T[i][(l + 1)..n] cat S[i][(i*(l - 1) + 2)..n] : i in [1..m]]);

/*
 * Semaev's summation polynomial for Weierstrass curves
 *
 * Source: page 15, http://dblp.org/rec/journals/iacr/HuangKY15
 */

E["f3"] := function(x0,x1,x2)
  a1 := Coefficients(E["curve"])[1];
  a2 := Coefficients(E["curve"])[2];
  a3 := Coefficients(E["curve"])[3];
  a4 := Coefficients(E["curve"])[4];
  a6 := Coefficients(E["curve"])[5];

  b2 := a1^2 + 4*a2;
  b4 := a1*a3 + 2*a4;
  b6 := a3^2 + 4*a6;
  b8 := a1^2*a6 - a1*a3*a4 + a2*a3^2 + 4*a2*a6 - a4^2;

  return x0^2*x1^2 - 2*x0^2*x1*x2 + x0^2*x2^2 - 2*x0*x1^2*x2 - 2*x0*x1*x2^2 - x0*x1*x2*b2 - x0*x1*b4 - x0*x2*b4 - x0*b6 + x1^2*x2^2 - x1*x2*b4 - x1*b6 - x2*b6 - b8;
end function;

