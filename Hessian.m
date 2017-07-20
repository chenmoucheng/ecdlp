/*
 * Hessian curves
 */

E := AssociativeArray();
E["form"] := "Hessian";
if not IsEmpty(Curves) then
  E0 := Curves[1];
  assert IsSimplifiedModel(E0["curve"]);
  V := Variety(Ideal({-27*R.1*(R.1^3 + 8) - a4,54*(R.1^6 - 20*R.1^3 - 8) - a6}))
       where _,_,_,a4,a6 is Explode(Coefficients(E0["curve"])) where R is PolynomialRing(k,1);
  assert not IsEmpty(V);
  d := Explode(Random(V));
  assert (3*d)^3 ne 1;
  E["curve"] := EllipticCurve([-27*d*(d^3 + 8),54*(d^6 - 20*d^3 - 8)]);
  _,cofactor := Check(E["curve"]);
else
  repeat
    repeat
      d := Random(k);
    until (3*d)^3 ne 1;
    E["curve"] := EllipticCurve([-27*d*(d^3 + 8),54*(d^6 - 20*d^3 - 8)]);
    ok,cofactor := Check(E["curve"]);
  until ok;
end if;
E["P"] := cofactor*Random(E["curve"](k));
E["order"] := Order(E["P"]);
E["curve"]; Coefficients(E["curve"]);
print "cofactor:",cofactor;
print "jInvariant:",jInvariant(E["curve"]);
print "Base point:",E["P"]; print "Order:",E["order"]; assert IsPrime(E["order"]);

// V: l-dimensional linear subspace of k over K that determines factor base FB

E["FBtoV"] := function(Q)
  assert Q ne E["curve"]!0;
  u := Q[1]/Q[3];
  v := Q[2]/Q[3];
  x := (36*(d^3 - 1) - v)/(6*(u + 9*d^2)) - d/2;
  y := (v + 36*(d^3 - 1))/(6*(u + 9*d^2)) - d/2;
  return x + y;
end function;

E["VtoFB"] := function(t)
  R<X,Y> := PolynomialRing(k,2);
  I := Ideal({X + Y - t,X^3 + Y^3 + 1 - 3*d*X*Y});
  Qs := [];
  for s in Variety(I) do
    x,y := Explode(s);
    u := 12*(d^3 - 1)/(d + x + y) - 9*d^2;
    v := 36*(y - x)*(d^3 - 1)/(d + x + y);
    Append(~Qs,E["curve"]![u,v]);
  end for;
  return Qs;
end function;

E["Iauxiliary"] := Ideal({s[i] - RewriteESP(t,i) : i in [1..m]}); Groebner(E["Iauxiliary"]);
E["Jcondition"] := Ideal(&cat[T[i][(l + 1)..n] cat S[i][(i*(l - 1) + 2)..n] : i in [1..m]]);

/*
 * Semaev's summation polynomial for Hessian curves
 *
 * Computed using the following MAGMA code:
 *
 * R<C0,C1,X1,Y1,T1,X2,Y2,T2,D,T> := PolynomialRing(Rationals(),10);
 * 
 * Z  := X2  *Y2 - X1  *Y1;
 * 
 * X3 := Y1^2*X2 - Y2^2*X1;
 * Y3 := X1^2*Y2 - X2^2*Y1;
 * T3 := X3 + Y3;
 * 
 * X4 := Y1^2*Y2 - X2^2*X1;
 * Y4 := X1^2*X2 - Y2^2*Y1;
 * T4 := X4 + Y4;
 * 
 * SN := func<t|t^3 + 1>;
 * SD := func<t|3*(t + D)>;
 * 
 * e1 := X1^3 + Y1^3 +   1 - 3*D*X1*Y1;
 * e2 := X2^3 + Y2^3 +   1 - 3*D*X2*Y2;
 * e3 := X3^3 + Y3^3 + Z^3 - 3*D*X3*Y3*Z;
 * e4 := X4^3 + Y4^3 + Z^3 - 3*D*X4*Y4*Z;
 * d1 := X1 + Y1 - T1;
 * d2 := X2 + Y2 - T2;
 * s1 := X1*Y1*SD(T1) - SN(T1);
 * s2 := X2*Y2*SD(T2) - SN(T2);
 * c0 := T3 * T4 - Z^2*C0;
 * c1 := T3 + T4 + Z  *C1;
 * 
 * I0 := Ideal({d1,d2,s1,s2,c0}); J0 := EliminationIdeal(I0,{T1,T2,D,C0}); G0 := Coefficients(Basis(J0)[1],C0);
 * I1 := Ideal({d1,d2,s1,s2,c1}); J1 := EliminationIdeal(I1,{T1,T2,D,C1}); G1 := Coefficients(Basis(J1)[1],C1);
 * 
 * g3 := G0[1]*G1[2] + G0[2]*G1[1]*T - G0[2]*G1[2]*T^2;
 * 
 * S<t1,t2,t3,d> := PolynomialRing(Rationals(),4);
 * phi := hom<R->S|[0,0,0,0,t1,0,0,t2,d,t3]>;
 * _,_,f3 := Explode(Factorization(phi(g3)))[1];
 */

E["f3"] := function(t1,t2,t3)
  return t1^2*t2^2*t3 + t1^2*t2^2*d + t1^2*t2*t3^2 + t1^2*t2*t3*d + t1^2*t3^2*d - t1^2 + t1*t2^2*t3^2 + t1*t2^2*t3*d + t1*t2*t3^2*d + 3*t1*t2*t3*d^2 + 2*t1*t2 + 2*t1*t3 + 2*t1*d + t2^2*t3^2*d - t2^2 + 2*t2*t3 + 2*t2*d - t3^2 + 2*t3*d + 3*d^2;
end function;

Append(~Curves,E); delete E;

