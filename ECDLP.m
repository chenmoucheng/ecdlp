/*
 * Solving ECDLP using Semaev's summation polynomials
 */

SetColumns(0);

// Utility functions

Degrees := function(F)
  D := [];
  for f in F do
    d := TotalDegree(f);
    if d eq 0 then continue; end if;
    if IsDefined(D,d) then D[d] +:= 1;
    else D[d] := 1; end if;
  end for;
  for d := 1 to #D do
    if not IsDefined(D,d) then D[d] := 0; end if;
  end for;

  return D;
end function;

InSupport := function(v,f)
  return Degree(f,v) gt 0;
end function;

RewriteESP := function(V,i)
  return hom<S->R|V>(ElementarySymmetricPolynomial(S,i)) where S is PolynomialRing(BaseRing(R),#V) where R is Universe(V);
end function;

// Substituting solution to easy part and computing GB

CoreGB := function(I)
  R := Generic(I);
  F := {f : f in Basis(I) | IsUnivariate(f)}; F_ := Seqset(Basis(I)) diff F;
  U := [R.i : i in [1..Rank(R)] | &and[not InSupport(R.i,f) : f in F] and &or[InSupport(R.i,f) : f in F_]];
  S := #K eq 2 select BooleanPolynomialRing(#U,"grevlex") else PolynomialRing(K,#U,"grevlex") where K is BaseRing(R);
  V := [S|];
  for i := 1 to Rank(R) do
    if R.i in U then
      Append(~V,S.Index(U,R.i));
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
  G := GroebnerBasis(Basis(J));
  SetVerbose("Faugere",0);

  H := [];
  D := 1;
  t0 := Cputime();
  H[D] := GroebnerBasis(Basis(J),D);
  print "Groebner basis time:",Cputime(t0),D,#H[D],"=",Degrees(H[D]);
  repeat
    D +:= 1;
    t0 := Cputime();
    H[D] := GroebnerBasis(Basis(J),D);
    print "Groebner basis time:",Cputime(t0),D,#H[D],"=",Degrees(H[D]);
    HH := {f : f in H[D] | Degree(f) lt D and NormalForm(f,H[D - 1]) ne 0};
    if not IsEmpty(HH) then
      print "  Gap degree and sizes:",D,#HH,"=",Degrees(HH);
    end if;
  until Seqset(G) eq Seqset(H[D]);

  return Ideal({phiSR(g) : g in G});
end function;

// Parameters

l  := 4;          print "l =", l;
m  := 2;          print "m =", m;
n  := 19;         print "n =", n;
q  := 241;        print "q =", q;
T2 := false;      print "T2 =", T2;
IX := true;       print "IX =", IX;

SetNthreads(1); print "Nthreads =",GetNthreads();

// Base and extension fields

K := FiniteField(q);
k<w> := ext<K|n>;
kK<W> := quo<PolynomialRing(K)|DefiningPolynomial(k,K)>;

isokK := hom<k->kK|W>;
isoKk := hom<kK->k|w>;

// Various structures for performing Weil descent

M := 3*m - 2;

R1 := PolynomialRing(k,M);
u := [R1.i : i in [       1 ..(  m - 2)]];
t := [R1.i : i in [(  m - 1)..(2*m - 2)]];
s := [R1.i : i in [(2*m - 1)..(3*m - 2)]];

R2 := PolynomialRing(kK,M*n);
phi12 := hom<R1->R2|isokK,[Evaluate(Polynomial([R2.((i - 1)*n + j) : j in [1..n]]),W) : i in [1..M]]>;

if q lt 65536 then
  R3,phi23 := R2/Ideal({R2.i^q - R2.i : i in [1..Rank(R2)]});
  phi32 := hom<R3->R2|[R2.i : i in [1..Rank(R2)]]>;
  phi22 := phi23 * phi32;
else
  phi22 := hom<R2->R2|[R2.i : i in [1..Rank(R2)]]>;
end if;

S1 := PolynomialRing(K,M*n);
S2 := quo<PolynomialRing(S1)|DefiningPolynomial(k,K)>;
isoRS := hom<R2->S2|hom<kK->S2|S2.1>,[S1.i : i in [1..Rank(S1)]]>;
isoSR := hom<S2->R2|hom<S1->R2|[R2.i : i in [1..Rank(R2)]]>,W>;

phi := phi12 * phi22 * isoRS;

U := [Coefficients(phi(x)) : x in u];
T := [Coefficients(phi(x)) : x in t];
S := [Coefficients(phi(x)) : x in s];

// From variety of S1's ideal to variable assignment in R1

psi := function(Z,x)
  return isoKk([Z[(i - 1)*n + j] : j in [1..n]]) where i is Index([R1.i : i in [1..M]],x);
end function;

// Curve-specific definitions

// load "bEdwards.m";
// load "Hessian.m";
load "Montgomery.m";
// load "tEdwards.m";
// load "Weierstrass.m";

E["f4"] := function(x0,x1,x2,x3)
  R<T,X0,X1,X2,X3> := PolynomialRing(k,5);
  f31 := E["f3"](T,X0,X1);
  f32 := E["f3"](T,X2,X3);
  f4 := Resultant(f31,f32,T);
  return hom<R->Parent(x0)|[0,x0,x1,x2,x3]>(f4);
end function;

E["f5"] := function(x0,x1,x2,x3,x4)
  R<T,X0,X1,X2,X3,X4> := PolynomialRing(k,6);
  f3 := E["f3"](T,X0,X1);
  f4 := E["f4"](T,X2,X3,X4);
  f5 := Resultant(f3,f4,T);
  return hom<R->Parent(x0)|[0,x0,x1,x2,x3,x4]>(f5);
end function;

E["f6"] := function(x0,x1,x2,x3,x4,x5)
  R<T,X0,X1,X2,X3,X4,X5> := PolynomialRing(k,7);
  f41 := E["f4"](T,X0,X1,X2);
  f42 := E["f4"](T,X3,X4,X5);
  f6 := Resultant(f41,f42,T);
  return hom<R->Parent(x0)|[0,x0,x1,x2,x3,x4,x5]>(f6);
end function;

// Weil descent

WeilDescent := function(I)
  t0 := Cputime();
  J := &+[ideal<S1|Coefficients(phi(f))> : f in Basis(I)];
  print "Weil descent time:",Cputime(t0);
  return J;
end function;

// Point decomposition

ECDLPDecompose := function(Qs)
  print "Decomposing",Qs;
  Q := Type(Qs) eq SeqEnum select &+Qs else Qs;
  if not IsPrime(Order(Q)) then return []; end if;
  z := E["FBtoV"](-Q);

  // Variables rewriting

  if m eq 2 then
    Isummation := Ideal({E["f3"](t[1],t[2],z)});
  else
    Isummation := Ideal({E["f3"](t[1],t[2],u[1])} join {E["f3"](u[i - 1],t[i + 1],u[i]) : i in [2..(m - 2)]} join {E["f3"](u[m - 2],t[m],z)});
  end if;
  print "Rewriting variables";
  SetVerbose("Faugere",2);
  if m eq 2 then
    Irewritten := EliminationIdeal(Ideal({E["f3"](t[1],t[2],               z)}) + E["Iauxiliary"],Seqset(s));
  elif m eq 3 then
    Irewritten := EliminationIdeal(Ideal({E["f4"](t[1],t[2],t[3],          z)}) + E["Iauxiliary"],Seqset(s));
  elif m eq 4 then
    Irewritten := EliminationIdeal(Ideal({E["f5"](t[1],t[2],t[3],t[4],     z)}) + E["Iauxiliary"],Seqset(s));
  elif m eq 5 then
    Irewritten := EliminationIdeal(Ideal({E["f6"](t[1],t[2],t[3],t[4],t[5],z)}) + E["Iauxiliary"],Seqset(s));
  else
    Irewritten := EliminationIdeal(Isummation + E["Iauxiliary"],Seqset(s));
  end if;
  SetVerbose("Faugere",0);
  if IX then Irewritten +:= E["Iauxiliary"]; end if;

  // Needs Isummation because u's information is eliminated in EliminationIdeal
  // Needs Jcondition because its information is eliminated in CoreGB
  Z := Variety(WeilDescent(Isummation + E["Iauxiliary"]) + CoreGB(WeilDescent(Irewritten) + E["Jcondition"]) + E["Jcondition"]);

  Qs := [];
  for z in Z do
    L := [[]];
    for i := 1 to m do
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

for point := 1 to 1 do
  print ""; print "Point A",point;
  repeat
    Qs := ECDLPDecompose([RandomFB() : i in [1..m]]);
  until not IsEmpty(Qs);
  Qs;

  for trial := 1 to 0 do
    print ""; print "Point B",point,trial; Qs := ECDLPDecompose(Random(Order(P))*P); Qs;
  end for;
end for;

