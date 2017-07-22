/*
 * Oakley-EC2N-3 curves
 */

E := AssociativeArray();
E["form"] := "Oakley-EC2N-3";
assert IsEmpty(Curves);
assert q^n eq 2^155;
k_ := ExtensionField<GF(2),X|X^155 + X^62 + 1>;
isok_ := hom<k_->k|Roots(R.1^155 + R.1^62 + 1)[1][1]> where R is PolynomialRing(k);
E["curve"] := EllipticCurve([1,A,0,0,B])
  where A is 0
  where B is isok_(k_.1^18 + k_.1^17 + k_.1^16 + k_.1^13 + k_.1^12 + k_.1^9 + k_.1^8 + k_.1^7 + k_.1^3 + k_.1^2 + k_.1 + 1);
E["P"] := 4*E["curve"]![isok_(k_.1^6 + k_.1^5 + k_.1^4 + k_.1^3 + k_.1 + 1),isok_(k_.1^8 + k_.1^7 + k_.1^6 + k_.1^3)];
E["order"] := Order(E["P"]);
E["curve"]; Coefficients(E["curve"]);
print "jInvariant:",jInvariant(E["curve"]);
print "Base point:",E["P"]; print "Order:",E["order"]; assert IsPrime(E["order"]);

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
  a1,a2,a3,a4,a6 := Explode(Coefficients(E["curve"]));

  b2 := a1^2 + 4*a2;
  b4 := a1*a3 + 2*a4;
  b6 := a3^2 + 4*a6;
  b8 := a1^2*a6 - a1*a3*a4 + a2*a3^2 + 4*a2*a6 - a4^2;

  return x0^2*x1^2 - 2*x0^2*x1*x2 + x0^2*x2^2 - 2*x0*x1^2*x2 - 2*x0*x1*x2^2 - x0*x1*x2*b2 - x0*x1*b4 - x0*x2*b4 - x0*b6 + x1^2*x2^2 - x1*x2*b4 - x1*b6 - x2*b6 - b8;
end function;

Append(~Curves,E); delete E;

