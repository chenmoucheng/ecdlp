/*
 * Binary Edwards curves
 */

E := AssociativeArray();
E["form"] := "bEdwards";
assert Characteristic(k) eq 2;
if not IsEmpty(Curves) then
  E_ := Curves[1]["curve"];
  assert IsSimplifiedModel(E_);
  a1,a2,a3,a4,a6 := Explode(Coefficients(E_));
  assert a1 eq 1 and a3 eq 0 and a4 eq 0;
  V := Variety(Ideal({R.1^2 + R.2 - a2,R.1^4*(R.1^4 + R.1^2 + R.2^2) - a6})) where R is PolynomialRing(k,2);
  assert not IsEmpty(V);
  d1,d2 := Explode(Random(V));
  assert d1 ne 0 and d2 ne d1^2 + d1;
  _,cofactor := Check(E_);
else
  repeat
    repeat
      d1 := Random(k);
      d2 := Random(k);
    until d1 ne 0 and d2 ne d1^2 + d1;
    E_ := EllipticCurve([1,d1^2 + d2,0,0,d1^4*(d1^4 + d1^2 + d2^2)]);
    assert jInvariant(E_) eq 1/(d1^4*(d1^4 + d1^2 + d2^2));
    ok,cofactor := Check(E_);
  until ok;
end if;
E["curve"],phi_,psi_ := SimplifiedModel(E_);
O_ := <k!0,k!0>;
E["P"] := cofactor*Random(E["curve"](k));
E["order"] := Order(E["P"]);
E["curve"]; Coefficients(E["curve"]);
print "jInvariant:",jInvariant(E["curve"]);
print "Base point:",E["P"]; print "Order:",E["order"]; assert IsPrime(E["order"]);
print "d1 =",d1; print "d2 =",d2;

// V: l-dimensional linear subspace of k over K that determines factor base FB

E["FBtoV"] := function(Q)
  if Q eq E["curve"]!0 then
    x,y := Explode(O_);
  else
    P := psi_(Q);
    u := P[1]/P[3];
    v := P[2]/P[3];
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
    if s eq O_ then
      Append(~Qs,E["curve"]!0);
    else
      x,y := Explode(s);
      u := d1*(d1^2 + d1 + d2)*(x + y)/(x*y + d1*(x + y));
      v := d1*(d1^2 + d1 + d2)*(x/(x*y + d1*(x + y)) + d1 + 1);
      Append(~Qs,phi_(E_![u,v]));
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

