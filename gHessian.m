/*
 * Generalized Hessian curves
 */

E := AssociativeArray();
E["form"] := "Hessian"; E["form"];
cofactor := 3;
repeat
  repeat
    c := Random(k);
    d := Random(k);
  until c ne 0 and d^3 ne 27;
  a1 := d/3;
  a3 := ((d/3)^3 - c)/27;
  E["curve"] := EllipticCurve([a1,0,a3,0,0]);
  order := Order(E["curve"](k));
  assert IsDivisibleBy(order,cofactor);
until IsPrime(Integers()!(order/cofactor));
P := cofactor*Random(E["curve"](k));
E["curve"]; Coefficients(E["curve"]);
print "jInvariant:",jInvariant(E["curve"]);
print "Base point:",P; print "Order:",Order(P); assert IsPrime(Order(P));

// V: l-dimensional linear subspace of k over K that determines factor base FB

zeta := AllRoots(k!1,3)[2];
E["FBtoV"] := function(Q)
  u := Q[1]/Q[3];
  v := Q[2]/Q[3];
  x :=   zeta     *a1 + (zeta - 1)*v/u + (2*zeta + 1)*a3/u;
  y := -(zeta + 1)*a1 - (zeta + 2)*v/u - (2*zeta + 1)*a3/u;
  return x + y;
end function;

E["VtoFB"] := function(t)
  // if t eq 0 then return []; end if;
  R<X,Y> := PolynomialRing(k,2);
  I := Ideal({X + Y - t,X^3 + Y^3 + c - d*X*Y});
  Qs := [];
  for s in Variety(I) do
    x := s[1];
    y := s[2];
    u :=             3*(2*zeta + 1)*a3/((zeta + 2)*x + (zeta - 1)*y - (2*zeta + 1)*a1);
    v := -(x + y + a1)*(2*zeta + 1)*a3/((zeta + 2)*x + (zeta - 1)*y - (2*zeta + 1)*a1);
    Append(~Qs,E["curve"]![u,v]);
  end for;
  return Qs;
end function;

E["Iauxiliary"] := Ideal({s[i] - RewriteESP(t,i) : i in [1..m]}); Groebner(E["Iauxiliary"]);
E["Jcondition"] := Ideal(&cat[T[i][(l + 1)..n] cat S[i][(i*(l - 1) + 2)..n] : i in [1..m]]);

/*
 * Semaev's summation polynomial for Hessian curves
 *
 * Source: Section 2, http://dblp.org/rec/journals/iacr/Farashahi10
 *
 * Computed using the following MAGMA code:
 *
 * R<C0,C1,X1,Y1,T1,X2,Y2,T2,C,D,T> := PolynomialRing(Rationals(),11);
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
 * SN := func<t|t^3 + C>;
 * SD := func<t|3*t + D>;
 * 
 * e1 := X1^3 + Y1^3 + C     - D*X1*Y1;
 * e2 := X2^3 + Y2^3 + C     - D*X2*Y2;
 * e3 := X3^3 + Y3^3 + C*Z^3 - D*X3*Y3*Z;
 * e4 := X4^3 + Y4^3 + C*Z^3 - D*X4*Y4*Z;
 * d1 := X1 + Y1 - T1;
 * d2 := X2 + Y2 - T2;
 * s1 := X1*Y1*SD(T1) - SN(T1);
 * s2 := X2*Y2*SD(T2) - SN(T2);
 * c0 := T3 * T4 - Z^2*C0;
 * c1 := T3 + T4 + Z  *C1;
 * 
 * SetVerbose("Faugere",2);
 * I0 := Ideal([d1,d2,s1,s2,c0]); J0 := EliminationIdeal(I0,{T1,T2,C,D,C0}); G0 := Coefficients(Basis(J0)[1],C0);
 * I1 := Ideal([d1,d2,s1,s2,c1]); J1 := EliminationIdeal(I1,{T1,T2,C,D,C1}); G1 := Coefficients(Basis(J1)[1],C1);
 * 
 * g3 := G0[1]*G1[2] + G0[2]*G1[1]*T - G0[2]*G1[2]*T^2;
 * 
 * S<t1,t2,t3,c,d> := PolynomialRing(Rationals(),5);
 * phi := hom<R->S|[0,0,0,0,t1,0,0,t2,c,d,t3]>;
 * f3 := Factorization(phi(g3))[3][1];
 */

E["f3"] := function(t1,t2,t3)
  return t1^2*t2^2*t3 + 1/3*t1^2*t2^2*d + t1^2*t2*t3^2 + 1/3*t1^2*t2*t3*d + 1/3*t1^2*t3^2*d - t1^2*c + t1*t2^2*t3^2 + 1/3*t1*t2^2*t3*d + 1/3*t1*t2*t3^2*d + 1/3*t1*t2*t3*d^2 + 2*t1*t2*c + 2*t1*t3*c + 2/3*t1*c*d + 1/3*t2^2*t3^2*d - t2^2*c + 2*t2*t3*c + 2/3*t2*c*d - t3^2*c + 2/3*t3*c*d + 1/3*c*d^2;
end function;

