/*
 * Edwards curves
 */

E := AssociativeArray();
E["form"] := "Edwards";
assert q ne 2;
repeat
  repeat
    c := 1;
    d := Random(k);
  until c*d*(1 - d*c^4) ne 0;
  a0 := 1/(1 - d*c^4);
  E["curve"] := QuadraticTwist(EllipticCurve([0,4/(1 - d*c^4) - 2,0,1,0]),a0);
  ok,cofactor := Check(E["curve"]);
until ok;
E["O"] := <k!0,k!c>;
E["Q"] := <k!0,k!-c>;
E["P"] := cofactor*Random(E["curve"](k));
E["curve"]; Coefficients(E["curve"]);
print "cofactor:",cofactor;
print "jInvariant:",jInvariant(E["curve"]);
print "Base point:",E["P"]; print "Order:",Order(E["P"]); assert IsPrime(Order(E["P"]));

// V: l-dimensional linear subspace of k over K that determines factor base FB

E["FBtoV"] := function(Q)
  if Q eq E["curve"]!0 then
    _,y := Explode(E["O"]);
  elif Q eq E["curve"]![0,0] then
    _,y := Explode(E["Q"]);
  else
    u := Q[1]/Q[3]/a0;
    // v := Q[2]/Q[3]/a0^2;
    // x := 2*c*u/v;
    y := c*(u - 1)/(u + 1);
  end if;
  return y;
end function;

E["VtoFB"] := function(t)
  R<X,Y> := PolynomialRing(k,2);
  I := Ideal({Y - t,X^2 + Y^2 - c^2*(1 + d*X^2*Y^2)});
  Qs := [];
  for s in Variety(I) do
    if s eq E["O"] then
      Append(~Qs,E["curve"]!0);
    elif s eq E["Q"] then
      Append(~Qs,E["curve"]![0,0]);
    else
      x,y := Explode(s);
      u := a0      *(c + y)/ (c - y);
      v := a0^2*2*c*(c + y)/((c - y)*x);
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
 * R<C0,C1,X1,Y1,X2,Y2,C,D,Y> := PolynomialRing(Rationals(),9);
 * 
 * Z  := C^2*(1 - (D*X1*X2*Y1*Y2)^2);
 * 
 * X3 := (X1*Y2 + X2*Y1)*(1 - D*X1*X2*Y1*Y2);
 * Y3 := (Y1*Y2 - X2*X1)*(1 + D*X1*X2*Y1*Y2);
 * 
 * X4 := (X1*Y2 - X2*Y1)*(1 + D*X1*X2*Y1*Y2);
 * Y4 := (Y1*Y2 + X2*X1)*(1 - D*X1*X2*Y1*Y2);
 * 
 * e1 := X1^2 + Y1^2 - (1 + D*X1^2*Y1^2);
 * e2 := X2^2 + Y2^2 - (1 + D*X2^2*Y2^2);
 * 
 * c0 := Y3 * Y4 - Z^2*C0;
 * c1 := Y3 + Y4 + Z  *C1;
 * 
 * I0 := Ideal({e1,e2,c0}); J0 := EliminationIdeal(I0,{Y1,Y2,C,D,C0}); G0 := Coefficients(Basis(J0)[1],C0);
 * I1 := Ideal({e1,e2,c1}); J1 := EliminationIdeal(I1,{Y1,Y2,C,D,C1}); G1 := Coefficients(Basis(J1)[1],C1);
 * 
 * g3 := G0[1]*G1[2] + G0[2]*G1[1]*Y - G0[2]*G1[2]*Y^2;
 * 
 * S<y1,y2,y3,c,d> := PolynomialRing(Rationals(),5);
 * phi := hom<R->S|[0,0,0,y1,0,y2,c,d,y3]>;
 * _,_,_,f3 := Explode(Factorization(phi(g3)))[1];
 */

E["f3"] := function(y1,y2,y3)
  return y1^2*y2^2*y3^2*c^4*d - y1^2*y2^2*d - y1^2*y3^2*c^4*d + y1^2 + 2*y1*y2*y3*c^2*d - 2*y1*y2*y3*c^2 - y2^2*y3^2*c^4*d + y2^2 + y3^2*c^4 - 1;
end function;

Append(~Curves,E); delete E;

