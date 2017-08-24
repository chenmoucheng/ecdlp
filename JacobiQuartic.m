/*
 * Jacobi quartic curves
 */

E := AssociativeArray();
E["form"] := "JacobiQuartic";
assert Characteristic(k) ne 2;
assert Characteristic(k) ne 3;
repeat
  repeat
    a := Random(k);
  until a*(a^2 - 1) ne 0;
  E["curve"] := QuadraticTwist(EllipticCurve([0,-2*a,0,a^2 - 1,0]),2);
  ok,cofactor := Check(E["curve"]);
until ok;
E["O"] := <k!0,k!1>;
E["Q"] := <k!0,k!-1>;
E["P"] := cofactor*Random(E["curve"](k));
E["order"] := Order(E["P"]);
E["curve"]; Coefficients(E["curve"]);
print "cofactor:",cofactor;
print "jInvariant:",jInvariant(E["curve"]);
print "Base point:",E["P"]; print "Order:",E["order"]; assert IsPrime(E["order"]);
print "a =",a;

// V: l-dimensional linear subspace of k over K that determines factor base FB

E["FBtoV"] := function(Q)
  if Q eq E["curve"]!0 then
    x,_ := Explode(E["O"]);
  elif Q eq E["curve"]![0,0] then
    x,_ := Explode(E["Q"]);
  else
    u := Q[1]/Q[3]/2;
    v := Q[2]/Q[3]/2^2;
    x := u/v;
    // y := (u - a)*(u/v)^2 - 1;
  end if;
  return x^2;
end function;

E["VtoFB"] := function(t)
  R<X,Y> := PolynomialRing(k,2);
  I := Ideal({X^2 - t,X^4 + 2*a*X^2 + 1 - Y^2});
  Qs := [];
  for s in Variety(I) do
    if s eq E["O"] then
      Append(~Qs,E["curve"]!0);
    elif s eq E["Q"] then
      Append(~Qs,E["curve"]![0,0]);
    else
      x,y := Explode(s);
      u := 2  *(a + (y + 1)/x^2);
      v := 2^2*(a + (y + 1)/x^2)/x;
      Append(~Qs,E["curve"]![u,v]);
    end if;
  end for;
  return Qs;
end function;

E["Iauxiliary"] := Ideal({s[i] - RewriteESP(t,i) : i in [1..m]}); Groebner(E["Iauxiliary"]);
E["Jcondition"] := Ideal(&cat[T[i][(l + 1)..n] cat S[i][(i*(l - 1) + 2)..n] : i in [1..m]]);

/*
 * Semaev's summation polynomial for Jacobi quartic curves
 *
 * R<y1,y2,x1,x2,x3,a> := PolynomialRing(Rationals(),6);
 * 
 * Z :=  1 - (x1*x2)^2;
 * 
 * X3 :=                  x1*y2 +     y1*x2;
 * Y3 := (1 + (x1*x2)^2)*(y1*y2 + 2*a*x1*x2) + 2*x1*x2*(x1^2 + x2^2);
 * 
 * X4 :=                  x1*y2 -     y1*x2;
 * Y4 := (1 + (x1*x2)^2)*(y1*y2 - 2*a*x1*x2) - 2*x1*x2*(x1^2 + x2^2);
 * 
 * e1 := x1^4 + 2*a*x1^2 + 1 - y1^2;
 * e2 := x2^4 + 2*a*x2^2 + 1 - y2^2;
 * 
 * I := EliminationIdeal(Ideal({e1,e2,X3^2 + X4^2 + x3}),{x1,x2,x3,a}); n1,d1 := Explode(Coefficients(Basis(I)[1],x3));
 * J := EliminationIdeal(Ideal({e1,e2,X3^2 * X4^2 + x3}),{x1,x2,x3,a}); n2,d2 := Explode(Coefficients(Basis(J)[1],x3));
 * _,_,f3 := Explode(Factorization(d1*d2*Z^4*x3^4 - d2*Z^2*n1*x3^2 + d1*n2)); f3[1];
 */

E["f3"] := function(x1,x2,x3)
  return x1^2*x2^2*x3^2 - 2*x1^2*x2^1*x3^1 + x1^2 - 2*x1^1*x2^2*x3^1 - 2*x1^1*x2^1*x3^2 - 8*x1^1*x2^1*x3^1*a - 2*x1^1*x2^1 - 2*x1^1*x3^1 + x2^2 - 2*x2^1*x3^1 + x3^2;
end function;

Append(~Curves,E); delete E;

