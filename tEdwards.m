/*
 * Twisted Edwards curves
 */

E := AssociativeArray();
E["form"] := "tEdwards";
assert Characteristic(k) ne 2;
if not IsEmpty(Curves) then
  E0 := Curves[1];
  assert IsWeierstrassModel(E0["curve"]);
  V := Variety(Ideal({(3 - R.1^2) - a4*(3*R.2^2),(2*R.1^3 - 9*R.1) - a6*(27*R.2^3)}))
       where _,_,_,a4,a6 is Explode(Coefficients(E0["curve"])) where R is PolynomialRing(k,2);
  assert not IsEmpty(V);
  A,B := Explode(Random(V));
  a := (A + 2)/B;
  d := (A - 2)/B;
  assert a ne 0 and d ne 0 and a ne d;
  a0 := 1/(a - d);
  E["curve"] := QuadraticTwist(EllipticCurve([0,4*a/(a - d) - 2,0,1,0]),a0);
  _,cofactor := Check(E["curve"]);
else
  repeat
    repeat
      a := Random(k);
      d := Random(k);
    until a ne 0 and d ne 0 and a ne d;
    a0 := 1/(a - d);
    E["curve"] := QuadraticTwist(EllipticCurve([0,4*a/(a - d) - 2,0,1,0]),a0);
    assert jInvariant(E["curve"]) eq 16*(a^2 + 14*a*d + d^2)^3/(a*d*(a - d)^4);
    ok,cofactor := Check(E["curve"]);
  until ok;
end if;
E["O"] := <k!0,k!1>;
E["Q"] := <k!0,k!-1>;
E["P"] := cofactor*Random(E["curve"](k));
E["order"] := Order(E["P"]);
E["curve"]; Coefficients(E["curve"]);
print "cofactor:",cofactor;
print "jInvariant:",jInvariant(E["curve"]);
print "Base point:",E["P"]; print "Order:",E["order"]; assert IsPrime(E["order"]);

// V: l-dimensional linear subspace of k over K that determines factor base FB

E["FBtoV"] := function(Q)
  if Q eq E["curve"]!0 then
    _,y := Explode(E["O"]);
  else
    u := Q[1]/Q[3]/a0;
    // v := Q[2]/Q[3]/a0^2;
    // x := 2*u/v;
    y := (u - 1)/(u + 1);
  end if;
  return y;
end function;

E["VtoFB"] := function(t)
  R<X,Y> := PolynomialRing(k,2);
  I := Ideal({Y - t,a*X^2 + Y^2 - (1 + d*X^2*Y^2)});
  Qs := [];
  for s in Variety(I) do
    if s eq E["O"] then
      Append(~Qs,E["curve"]!0);
    elif s eq E["Q"] then
      Append(~Qs,E["curve"]![0,0]);
    else
      x,y := Explode(s);
      u := a0  *  (1 + y)/   (1 - y);
      v := a0^2*2*(1 + y)/(x*(1 - y));
      Append(~Qs,E["curve"]![u,v]);
    end if;
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

Append(~Curves,E); delete E;

