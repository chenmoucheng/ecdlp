/*
 * Solving ECDLP using Semaev's summation polynomials
 */

// Utility functions

SetColumns(0);

InSupport := function(v,f)
  return Degree(f,v) gt 0;
end function;

RewriteESP := function(V,i)
  return hom<S->R|V>(ElementarySymmetricPolynomial(S,i)) where S is PolynomialRing(BaseRing(R),#V) where R is Universe(V);
end function;

// Substituting solution to easy part and computing GB

EasyGB := function(I)
  R := Generic(I);
  F := {f : f in Basis(I) | IsUnivariate(f)}; F_ := Seqset(Basis(I)) diff F;
  U := [R.i : i in [1..Rank(R)] | &and[not InSupport(R.i,f) : f in F] and &or[InSupport(R.i,f) : f in F_]];
  S := #K eq 2 select BooleanPolynomialRing(#U,"grevlex") else PolynomialRing(K,#U,"grevlex") where K is BaseRing(R);
  V := [S|]; v := 0;
  for i in [1..Rank(R)] do
    if R.i in U then
      v := v + 1;
      Append(~V,S.v);
    else
      G := {UnivariatePolynomial(f) : f in F | InSupport(R.i,f)};
      x := IsEmpty(G) select Random(BaseRing(R)) else Random(Roots(Random(G)))[1];
      Append(~V,x);
    end if;
  end for;
  phiRS := hom<R->S|V>;
  phiSR := hom<S->R|U>;
  J := Ideal({g : f in Basis(I) | g ne 0 where g is phiRS(f)});

  SetVerbose("Faugere",2);
  G := GroebnerBasis(J);
  SetVerbose("Faugere",0);

  return Ideal({phiSR(g) : g in G});
end function;

// Parameters

l := 5;   print "l =", l;
m := 3;   print "m =", m;
n := 17;  print "n =", n;
q := 2;   print "q =", q;

// Base and extension fields

K := FiniteField(q);
k<w> := ext<K|n>;
kK<W> := quo<PolynomialRing(K)|DefiningPolynomial(k,K)>;

isokK := hom<k->kK|W>;
isoKk := hom<kK->k|w>;

// Various structures for performing Weil descent

M := 3*m - 1;

R1 := PolynomialRing(k,M);
u := [R1.i : i in [       1 ..(  m - 2)]];
t := [R1.i : i in [(  m - 1)..(2*m - 2)]];
s := [R1.i : i in [(2*m - 1)..(3*m - 2)]];
v := [R1.M];

R2 := PolynomialRing(kK,M*n);
phi12 := hom<R1->R2|isokK,[Evaluate(Polynomial([R2.((i - 1)*n + j) : j in [1..n]]),W) : i in [1..M]]>;

R3,phi23 := R2/Ideal({R2.i^q - R2.i : i in [1..Rank(R2)]});
phi32 := hom<R3->R2|[R2.i : i in [1..Rank(R2)]]>;

S1 := PolynomialRing(K,M*n);
S2 := quo<PolynomialRing(S1)|DefiningPolynomial(k,K)>;
isoRS := hom<R2->S2|hom<kK->S2|S2.1>,[S1.i : i in [1..Rank(S1)]]>;
isoSR := hom<S2->R2|hom<S1->R2|[R2.i : i in [1..Rank(R2)]]>,W>;

phi := phi12 * phi23 * phi32 * isoRS;

U := [Coefficients(phi(x)) : x in u];
T := [Coefficients(phi(x)) : x in t];
S := [Coefficients(phi(x)) : x in s];

// From variety of S1's ideal to variable assignment in R1

psi := function(Z,x)
  return isoKk([Z[(i - 1)*n + j] : j in [1..n]]) where i is Index([R1.i : i in [1..M]],x);
end function;

// START

// Elliptic curve

E := AssociativeArray();
E["form"] := "bEdwards"; E["form"];
assert q eq 2;
repeat
  d1 := Random(k);
  d2 := Random(k);
until d1 ne 0 and d2 ne d1^2 + d1;
E["curve"] := EllipticCurve([1,d1^2 + d2,0,0,d1^4*(d1^4 + d1^2 + d2^2)]);
E["curve"]; Coefficients(E["curve"]);

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

// END

// Variables rewriting

if m eq 2 then
  Isummation := Ideal({E["f3"](t[1],t[2],v[1])});
else
  Isummation := Ideal({E["f3"](t[1],t[2],u[1])} join {E["f3"](u[i - 1],t[i + 1],u[i]) : i in [2..(m - 2)]} join {E["f3"](u[m - 2],t[m],v[1])});
end if;
print "Rewriting variables";
SetVerbose("Faugere",2);
Irewritten := EliminationIdeal(Isummation + E["Iauxiliary"],Seqset(s cat v)) + E["Iauxiliary"];
SetVerbose("Faugere",0);
print "";

// Weil descent

WeilDescent := function(I)
  phi12 := hom<R1->R2|isokK,[Evaluate(Polynomial([R2.ind : j in [1..n] | not S1.ind in E["Jcondition"] where ind := (i - 1)*n + j]),W) : i in [1..M]]>;
  phi := phi12 * phi23 * phi32 * isoRS;
  t0 := Cputime();
  J := &+[ideal<S1|Coefficients(phi(f))> : f in Basis(I)];
  print "Weil descent time:",Cputime(t0);
  return J;
end function;

// Point decomposition

ECDLPDecompose := function(Qs)
  print "Decomposing",Qs;
  Q := Type(Qs) eq SeqEnum select &+Qs else Qs;
  z := E["FBtoV"](-Q);
  phi := func<I|Ideal([hom<R1->R1|Append([R1.i : i in [1..(M - 1)]],z)>(f) : f in Basis(I)])>;

  // Needs Isummation because u's information is eliminated in EliminationIdeal
  // Needs Jcondition because its information is eliminated in EasyGB
  Z := Variety(WeilDescent(Ideal(v[1] - z) + phi(Isummation)) + EasyGB(WeilDescent(phi(Irewritten)) + E["Jcondition"]) + E["Jcondition"]);

  Qs := [];
  for z in Z do
    L := [[]];
    for i in [1..m] do
      L := [Append(Ps,PP) : Ps in L, PP in E["VtoFB"](psi(z,t[i]))];
    end for;
    Qs cat:= [Ps : Ps in L | &+Ps eq Q];
  end for;

  return Qs;
end function;

// Random elements from V and FB

RandomV := function()
  repeat
    v := isoKk([Random(K) : i in [1..l]]);
  until v ne 0;
  return v;
end function;

RandomFB := function()
  repeat
    Qs := E["VtoFB"](RandomV());
  until not IsEmpty(Qs);
  return Random(Qs);
end function;

// Experiments

repeat
  P := Random(E["curve"](k));
until Order(P) ge q^(n - 4);
print "Base point P",P; print "Order",Order(P);

for point in [1..1] do
  print "Point A",point; Qs := ECDLPDecompose([RandomFB() : i in [1..m]]); Qs; assert not IsEmpty(Qs);

  for trial in [1..1] do
    print "Point B",point,trial; Qs := ECDLPDecompose(Random(Order(P))*P); Qs;
  end for;
end for;

