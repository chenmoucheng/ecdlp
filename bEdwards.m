/*
 * Binary Edwards curves
 */

E := AssociativeArray();
E["form"] := "bEdwards";
assert q eq 2;
repeat
  repeat
    d1 := Random(k);
    d2 := Random(k);
  until d1 ne 0 and d2 ne d1^2 + d1;
  E["curve"] := EllipticCurve([1,d1^2 + d2,0,0,d1^4*(d1^4 + d1^2 + d2^2)]);
  Q := Random(E["curve"](k));
  p := fs[#fs][1] where fs is Factorization(Order(Q));
until p ge q^(n - 4);
E["curve"]; Coefficients(E["curve"]);
cofactor := Integers()!(Order(Q)/p);
P := cofactor*Q;
print "Base point:",P; print "Order:",Order(P); assert IsPrime(Order(P));

// V: l-dimensional linear subspace of k over K that determines factor base FB

E["FBtoV"] := function(Q)
  u := Q[1]/Q[3];
  v := Q[2]/Q[3];
  x := d1*(u + d1^2 + d1 + d2)/(u + v + (d1^2 + d1)*(d1^2 + d1 + d2));
  y := d1*(u + d1^2 + d1 + d2)/(    v + (d1^2 + d1)*(d1^2 + d1 + d2));
  return x + y;
end function;

E["VtoFB"] := function(t)
  if t eq 0 then return []; end if;
  R<X,Y> := PolynomialRing(k,2);
  I := Ideal({X + Y - t,d1*(X + Y) + d2*(X^2 + Y^2) - (X*Y + X*Y*(X + Y) + X^2*Y^2)});
  Qs := [];
  for s in Variety(I) do
    x := s[1];
    y := s[2];
    u := d1*(d1^2 + d1 + d2)*(x + y)/(x*y + d1*(x + y));
    v := d1*(d1^2 + d1 + d2)*(x/(x*y + d1*(x + y)) + d1 + 1);
    Append(~Qs,E["curve"]![u,v]);
  end for;
  return Qs;
end function;

E["Iauxiliary"] := Ideal({s[i] - RewriteESP(t,i) : i in [1..m]});
E["Jcondition"] := Ideal(&cat[T[i][(l + 1)..n] cat S[i][(i*(l - 1) + 2)..n] : i in [1..m]]);

// Semaev's summation polynomial

E["f3"] := function(t1,t2,t3)
  return (d2*t1^2*t2^2 + d1*(t1^2*t2 + t1*t2^2 + t1*t2 + d1))*t3^2 + d1*(t1^2*t2^2 + t1^2*t2 + t1*t2^2 + t1*t2)*t3 +d1^2*(t1^2 + t2^2);
end function;

