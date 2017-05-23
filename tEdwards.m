/*
 * Twisted Edwards curves
 */

E := AssociativeArray();
E["form"] := "tEdwards"; E["form"];
assert q ne 2;
repeat
  repeat
    a := Random(k);
    d := Random(k);
  until a ne 0 and d ne 0 and a ne d;
  a0 := 1/(a - d);
  E["curve"] := QuadraticTwist(EllipticCurve([0,4*a/(a - d) - 2,0,1,0]),a0);
  assert jInvariant(E["curve"]) eq 16*(a^2 + 14*a*d + d^2)^3/(a*d*(a - d)^4);
  Q := Random(E["curve"](k));
  cofactor := Integers()!(Order(Q)/fs[#fs][1]) where fs is Factorization(Order(Q));
  P := cofactor*Q;
until cofactor lt 16;
E["curve"]; Coefficients(E["curve"]);
print "Base point:",P; print "Order:",Order(P); assert IsPrime(Order(P));

// V: l-dimensional linear subspace of k over K that determines factor base FB

E["FBtoV"] := function(Q)
  u := Q[1]/Q[3]/a0;
  // v := Q[2]/Q[3]/(a0^2);
  // x := 2*u/v;
  y := (u - 1)/(u + 1);
  return y;
end function;

E["VtoFB"] := function(t)
  R<X,Y> := PolynomialRing(k,2);
  I := Ideal({Y - t, a*X^2 + Y^2 - (1 + d*X^2*Y^2)});
  Qs := [];
  for s in Variety(I) do
    x := s[1];
    y := s[2];
    u := a0  *  (1 + y)/   (1 - y);
    v := a0^2*2*(1 + y)/(x*(1 - y));
    Append(~Qs,E["curve"]![u,v]);
  end for;
  return Qs;
end function;

E["Iauxiliary"] := Ideal({s[i] - RewriteESP(t,i) : i in [1..m]}); Groebner(E["Iauxiliary"]);
E["Jcondition"] := Ideal(&cat[T[i][(l + 1)..n] cat S[i][(i*(l - 1) + 2)..n] : i in [1..m]]);

/*
 * Semaev's summation polynomial for twisted Edwards curves
 *
 * Source: page 8, http://dblp.org/rec/journals/joc/FaugereGHR14
 */

E["f3"] := function(y1,y2,y3)
  return (y1^2*y2^2 - y1^2 - y2^2 + a/d)*y3^2 + 2*(d - a)/d*y1*y2*y3 + (a/d)*(y1^2 + y2^2 - 1) - y1^2*y2^2;
end function;

