/*
 * Binary Edwards curves
 */

E := AssociativeArray();
E["form"] := "bEdwards";
assert q eq 2;
repeat
  repeat
    d1 := Random(k);
    d2 := d1;
  until d1 ne 0 and d2 ne d1^2 + d1;
  E["curve"] := EllipticCurve([1,d1^2 + d2,0,0,d1^4*(d1^4 + d1^2 + d2^2)]);
  assert jInvariant(E["curve"]) eq 1/(d1^4*(d1^4 + d1^2 + d2^2));
  ok,cofactor := Check(E["curve"]);
until ok;
E["O"] := <k!0,k!0>;
E["P"] := cofactor*Random(E["curve"](k));
E["curve"]; Coefficients(E["curve"]);
print "jInvariant:",jInvariant(E["curve"]);
print "Base point:",E["P"]; print "Order:",Order(E["P"]); assert IsPrime(Order(E["P"]));

// V: l-dimensional linear subspace of k over K that determines factor base FB

E["FBtoV"] := function(Q)
  if Q eq E["curve"]!0 then
    x,y := Explode(E["O"]);
  else
    u := Q[1]/Q[3];
    v := Q[2]/Q[3];
    x := d1*(u + d1^2 + d1 + d2)/(u + v + (d1^2 + d1)*(d1^2 + d1 + d2));
    y := d1*(u + d1^2 + d1 + d2)/(    v + (d1^2 + d1)*(d1^2 + d1 + d2));
  end if;
  return x + y;
end function;

E["VtoFB"] := function(t)
  R<X,Y> := PolynomialRing(k,2);
  I := Ideal({X + Y - t,d1*(X + Y) + d2*(X^2 + Y^2) - (X*Y + X*Y*(X + Y) + X^2*Y^2)});
  Qs := [];
  for s in Variety(I) do
    if s eq E["O"] then
      Append(~Qs,E["curve"]!0);
    else
      x,y := Explode(s);
      u := d1*(d1^2 + d1 + d2)*(x + y)/(x*y + d1*(x + y));
      v := d1*(d1^2 + d1 + d2)*(x/(x*y + d1*(x + y)) + d1 + 1);
      Append(~Qs,E["curve"]![u,v]);
    end if;
  end for;
  return Qs;
end function;

E["Iauxiliary"] := Ideal({s[i] - RewriteESP(t,i) : i in [1..m]}); Groebner(E["Iauxiliary"]);
E["Jcondition"] := Ideal(&cat[T[i][(l + 1)..n] cat S[i][(i*(l - 1) + 2)..n] : i in [1..m]]);

/*
 * Semaev's summation polynomial for binary Edwards curves
 *
 * Source: page 7, http://dblp.org/rec/journals/iacr/GalbraithG14
 */

E["f3"] := function(t1,t2,t3)
  return (d2*t1^2*t2^2 + d1*(t1^2*t2 + t1*t2^2 + t1*t2 + d1))*t3^2 + d1*(t1^2*t2^2 + t1^2*t2 + t1*t2^2 + t1*t2)*t3 +d1^2*(t1^2 + t2^2);
end function;

Append(~Curves,E); delete E;

