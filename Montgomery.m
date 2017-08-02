/* 
 * Montgomery curves
 */

assert Characteristic(k) ne 2;
if T2 then
  assert IsDivisibleBy(n,l);
end if;

E := AssociativeArray();
E["form"] := "Montgomery";
if not IsEmpty(Curves) then
  E0 := Curves[1];
  assert IsSimplifiedModel(E0["curve"]);
  V := Variety(Ideal({(3 - R.1^2) - a4*(3*R.2^2),(2*R.1^3 - 9*R.1) - a6*(27*R.2^3)}))
       where _,_,_,a4,a6 is Explode(Coefficients(E0["curve"])) where R is PolynomialRing(k,2);
  assert not IsEmpty(V);
  A,B := Explode(Random(V));
  assert B*(A^2 - 4) ne 0;
  E["curve"] := EllipticCurve([(3 - A^2)/(3*B^2),(2*A^3 - 9*A)/(27*B^3)]);
  _,cofactor := Check(E["curve"]);
else
  repeat
    repeat
      A := Random(k);
      B := Random(k);
    until B*(A^2 - 4) ne 0;
    E["curve"] := EllipticCurve([(3 - A^2)/(3*B^2),(2*A^3 - 9*A)/(27*B^3)]);
    ok,cofactor := Check(E["curve"]);
  until ok;
end if;
E["P"] := cofactor*Random(E["curve"](k));
E["order"] := Order(E["P"]);
E["curve"]; Coefficients(E["curve"]);
print "cofactor:",cofactor;
print "jInvariant:",jInvariant(E["curve"]);
print "Base point:",E["P"]; print "Order:",E["order"]; assert IsPrime(E["order"]);
print "A =",A; print "B =",B;

// V: l-dimensional linear subspace of k over K that determines factor base FB

E["FBtoV"] := function(Q)
  assert Q ne E["curve"]!0;
  u := Q[1]/Q[3];
  // v := Q[2]/Q[3];
  x := B*u - 1/3*A;
  // y := B*v;
  return x;
end function;

E["VtoFB"] := function(t)
  R<X,Y> := PolynomialRing(k,2);
  Z := Roots(Evaluate(f,[t,R.1]))
    where f is -B*Y^2 + X^3 + A*X^2 + X
    where R is PolynomialRing(k);
  return [E["curve"]![t/B + A/(3*B),z[1]/B] : z in Z];
end function;

// The numerators after clearing the denominators in s[i]
RewriteT2ESP := function(Vars,i)
  R := Universe(Vars);
  S := PolynomialRing(BaseRing(R),#Vars);
  map := hom<S->R|[Vars[j]^2+1 : j in [1..m]]>;
  Term := Terms(ElementarySymmetricPolynomial(S, i));
  if i eq #Vars then
    return map(Term)[1];
  else
    Poly :=  R ! 0;
    for j in Term do
      Diff := {S.i : i in [1..#Vars]} diff SequenceToSet([Factorization(j)[l][1] : l in[1..i] ]);
      Poly +:= map(j) * &*hom<S->R|Vars>(SetToSequence(Diff));
    end for;
  end if;
  return Poly;
end function;

E["Iauxiliary"] := T2 select Ideal({RewriteESP(t,m)*s[i] - RewriteT2ESP(t,i) : i in [1..m]}) else Ideal({s[i] - RewriteESP(t,i) : i in [1..m]}); Groebner(E["Iauxiliary"]);
E["Jcondition"] := Ideal(&cat[T[i][(l + 1)..n] cat S[i][(i*(l - 1) + 2)..n] : i in [1..m]]);

// Semaev's summation polynomial for Montgomery curves

E["f3"] := function(x0,x1,x2)
  return x0^2*x1^2 - 2*x0^2*x1*x2 + x0^2*x2^2 - 2*x0*x1^2*x2 - 2*x0*x1*x2^2 - 4*x0*x1*x2*A - 2*x0*x1 - 2*x0*x2 + x1^2*x2^2 - 2*x1*x2 + 1;
end function;

Append(~Curves,E); delete E;

