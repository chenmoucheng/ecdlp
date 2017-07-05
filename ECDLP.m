/*
 * Solving ECDLP using Semaev's summation polynomials
 */

// System settings

SetColumns(0);
SetNthreads(1);
SetVerbose("FGLM",2);
print "Nthreads =",GetNthreads();

// Core solving logic

load "CoreSolve.m";

// Parameters

h  := 1;          print "h =",h;
l  := 2;          print "l =",l;
m  := 3;          print "m =",m;
n  := 5;          print "n =",n;
q  := 2;          print "q =",q;
T2 := false;      print "T2 =",T2;
IX := true;       print "IX =",IX;
Al := "SAGB";     print "Al =",Al;

// Symmetrization is free in subfield (l = 1), so no need to include X variables (IX = false)

assert not (l eq 1 and IX);
elim := (l eq 1) or (l gt 1 and IX);

// Base and extension fields

K := FiniteField(q);
k<w> := ext<K|n>;
kK<W> := quo<PolynomialRing(K)|DefiningPolynomial(k,K)>;

isokK := hom<k->kK|W>;
isoKk := hom<kK->k|w>;

// Various structures for performing Weil restriction

M := 3*m - 1;

R1 := PolynomialRing(k,M);
u := [R1.i : i in [       1 ..(  m - 2)]];
t := [R1.i : i in [(  m - 1)..(2*m - 2)]];
s := [R1.i : i in [(2*m - 1)..(3*m - 2)]];
r :=  R1.M;

R2 := PolynomialRing(kK,M*n);
phi12 := hom<R1->R2|isokK,F>
         where F is [Evaluate(Polynomial([R2.((i - 1)*n + j) : j in [1..n]]),W) : i in [1..M]];

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
R :=  Coefficients(phi(r));

// From variety of S1's ideal to variable assignment in R1

psi := function(Z,x)
  return isoKk([Z[(i - 1)*n + j] : j in [1..n]]) where i is Index([R1.i : i in [1..M]],x);
end function;

// Curve-specific definitions

RewriteESP := function(V,i)
  return hom<S->R|V>(ElementarySymmetricPolynomial(S,i))
         where S is PolynomialRing(BaseRing(R),#V) where R is Universe(V);
end function;

curves := [];

// load "bEdwards.m";
// load "Edwards.m";
// load "gHessian.m";
// load "Hessian.m";
// load "Montgomery.m";
// load "tEdwards.m";
load "Weierstrass.m";

for i in [1..#curves] do
  E := curves[i];

curves[i]["f4"] := function(x0,x1,x2,x3)
  R<T,X0,X1,X2,X3> := PolynomialRing(k,5);
  f31 := E["f3"](T,X0,X1);
  f32 := E["f3"](T,X2,X3);
  f4 := Resultant(f31,f32,T);
  return hom<R->Parent(x0)|[0,x0,x1,x2,x3]>(f4);
end function;

curves[i]["f5"] := function(x0,x1,x2,x3,x4)
  R<T,X0,X1,X2,X3,X4> := PolynomialRing(k,6);
  f3 := E["f3"](T,X0,X1);
  f4 := E["f4"](T,X2,X3,X4);
  f5 := Resultant(f3,f4,T);
  return hom<R->Parent(x0)|[0,x0,x1,x2,x3,x4]>(f5);
end function;

curves[i]["f6"] := function(x0,x1,x2,x3,x4,x5)
  R<T,X0,X1,X2,X3,X4,X5> := PolynomialRing(k,7);
  f41 := E["f4"](T,X0,X1,X2);
  f42 := E["f4"](T,X3,X4,X5);
  f6 := Resultant(f41,f42,T);
  return hom<R->Parent(x0)|[0,x0,x1,x2,x3,x4,x5]>(f6);
end function;

// Semaev's summation ideal

if m eq 2 then
  curves[i]["Isummation"] := Ideal({E["f3"](t[1],t[2],r)});
else
  curves[i]["Isummation"] := Ideal({E["f3"](t[1],    t[2],    u[1])}
                 join {E["f3"](u[i - 1],t[i + 1],u[i]) : i in [2..(m - 2)]}
                 join {E["f3"](u[m - 2],t[m],    r)});
end if;
end for;

// Weil restriction

WeilRestriction := function(I)
  t0 := Cputime();
  J := &+[ideal<S1|Coefficients(phi(f))> : f in Basis(I)];
  print "Weil restriction time:",Cputime(t0);
  return J;
end function;

// Point decomposition

ECDLPDecompose := function(E,Q : Al := "All",Verbose := false)
  print "Decomposing",Q;
  if not IsPrime(Order(Q)) then return []; end if;

  z := E["FBtoV"](-Q);
  Icondition := Ideal({r - z});
  J := WeilRestriction(E["Isummation"] + Icondition + E["Iauxiliary"]) + E["Jcondition"];

  if h ge 0 then
    Z := C cat [K!0 : i in [(#C + 1)..n]] where C is Coefficients(phi(z));
    Jcondition := ideal<S1|{R[i] - Z[i] : i in [1..h]}>;
    P,iota := CoreIdeal(WeilRestriction(E["Isummation"]) + E["Jcondition"] + Jcondition);

    t0 := Cputime();
    Jb := Ideal({iota(f) : f in GroebnerBasis(Basis(P),4)});
    Zb := Variety(J + Jb);
    print "Batch decomposition time:",Cputime(t0);
  end if;

  print "Rewriting variables";
  if not elim then
    print "  ... skipped";
    Irewritten := E["Isummation"] + Icondition;
  else
    case m:
      when 2:
        I := Ideal({E["f3"](t[1],t[2],r)});
      when 3:
        I := Ideal({E["f4"](t[1],t[2],t[3],r)});
      when 4:
        I := Ideal({E["f5"](t[1],t[2],t[3],t[4],r)});
      when 5:
        I := Ideal({E["f6"](t[1],t[2],t[3],t[4],t[5],r)});
      else
        I := E["Isummation"];
    end case;
    b := GetVerbose("Faugere"); SetVerbose("Faugere",Verbose select 2 else 0);
    Irewritten := EliminationIdeal(I + Icondition + E["Iauxiliary"],Seqset(s));
    SetVerbose("Faugere",0);
  end if;
  if IX then Irewritten +:= E["Iauxiliary"]; end if;

  Jp := WeilRestriction(Irewritten) + E["Jcondition"];
  t0 := Cputime();
  Zp := CoreVariety(J,Jp : Al := Al,Verbose := Verbose);
  print "Point decomposition time:",Cputime(t0);

  if h ge 0 then
    assert Seqset(Zb) eq Seqset(Zp);
  end if;

  Qs := [];
  for z in Zp do
    L := [[]];
    for i := 1 to m do
      L := [Append(Ps,PP) : Ps in L, PP in E["VtoFB"](psi(z,t[i]))];
    end for;
    Qs cat:= [Ps : Ps in L | &+Ps eq Q];
  end for;

  return Qs;
end function;

// Random elements from FB

RandomFB := function(E)
  repeat
    Qs := E["VtoFB"](isoKk([Random(K) : i in [1..l]]));
  until not IsEmpty(Qs);
  return Random(Qs);
end function;

// Experiments

for E in curves do
  print ""; print "Working on",E["form"],E["curve"];

for point := 1 to 1 do
  print ""; print "Point A",point;
  repeat
    Ps := [RandomFB(E) : i in [1..m]]; Ps;
    Qs := ECDLPDecompose(E,&+Ps : Verbose := true);
  until not IsEmpty(Qs);
  Qs;

  success := 0;
  ntrials := 10;
  for trial := 1 to ntrials do
    print ""; print "Point B",point,trial;
    Qs := ECDLPDecompose(E,Random(Order(E["P"]))*E["P"] : Al := Al);
    if not IsEmpty(Qs) then
      Qs; success +:= 1;
    end if;
  end for;
  if ntrials gt 0 then
    print ""; print "Success probability:",success/ntrials;
  end if;
end for;
end for;

