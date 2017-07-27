/*
 * Solving ECDLP using Semaev's summation polynomials
 */

// System settings

SetColumns(0);
SetNthreads(1);
print "Nthreads =",GetNthreads();

SomethingBig := 2^12;
SomethingBIG := 2^24;

// Core solving logic

load "CoreSolve.m";

// Parameters

h  := -1;         print "h =",h;
l  := 2;          print "l =",l;
m  := 2;          print "m =",m;
n  := 5;          print "n =",n;
q  := 251;        print "q =",q;
T2 := false;      print "T2 =",T2;
IX := true;       print "IX =",IX;
Al := "Groebner"; print "Al =",Al;

ntrials := 2; print "ntrials =",ntrials;

// Symmetrization is free in subfield (l = 1), so no need to include X variables (IX = false)

assert not (l eq 1 and IX);
elim := (l eq 1) or (l gt 1 and IX);

// Base and extension fields

ind := function(x)
  k := Parent(x);
  if IsPrimeField(k) then
    return hom<k->Integers()|>(x);
  end if;
  return Evaluate(PolynomialRing(Integers())![$$(y) : y in ElementToSequence(x)],#BaseField(k));
end function;

K := FiniteField(q);
k<w> := RandomExtension(K,n);
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

if q lt SomethingBig then
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

Check := function(E)
  order := Order(E(k));
  cofactor := Integers()!(order/fs[#fs][1]) where fs is Factorization(order);
  return cofactor le 200 and IsDivisibleBy(cofactor,12),cofactor;
end function;

RewriteESP := function(V,i)
  return hom<S->R|V>(ElementarySymmetricPolynomial(S,i))
         where S is PolynomialRing(BaseRing(R),#V) where R is Universe(V);
end function;

Curves := [];

// load "OakleyEC2N3.m";

// load "bEdwards.m";
// load "Edwards.m";
// load "gHessian.m";
load "Hessian.m";
load "Montgomery.m";
load "tEdwards.m";
load "Weierstrass.m";

// Semaev's summation polynomials

Semaev3 := function(E,x0,x1,x2)
  return E["f3"](x0,x1,x2);
end function;

Semaev4 := function(E,x0,x1,x2,x3)
  R<T,X0,X1,X2,X3> := PolynomialRing(k,5);
  f31 := Semaev3(E,T,X0,X1);
  f32 := Semaev3(E,T,X2,X3);
  f4 := Resultant(f31,f32,T);
  return hom<R->Parent(x0)|[0,x0,x1,x2,x3]>(f4);
end function;

Semaev5 := function(E,x0,x1,x2,x3,x4)
  R<T,X0,X1,X2,X3,X4> := PolynomialRing(k,6);
  f3 := Semaev3(E,T,X0,X1);
  f4 := Semaev4(E,T,X2,X3,X4);
  f5 := Resultant(f3,f4,T);
  return hom<R->Parent(x0)|[0,x0,x1,x2,x3,x4]>(f5);
end function;

Semaev6 := function(E,x0,x1,x2,x3,x4,x5)
  R<T,X0,X1,X2,X3,X4,X5> := PolynomialRing(k,7);
  f41 := Semaev4(E,T,X0,X1,X2);
  f42 := Semaev4(E,T,X3,X4,X5);
  f6 := Resultant(f41,f42,T);
  return hom<R->Parent(x0)|[0,x0,x1,x2,x3,x4,x5]>(f6);
end function;

// Semaev's summation ideal

for i in [1..#Curves] do
  if m eq 2 then
    Curves[i]["Isummation"] := Ideal({Curves[i]["f3"](t[1],    t[2],    r)});
  else
    Curves[i]["Isummation"] := Ideal({Curves[i]["f3"](t[1],    t[2],    u[1])}
                                join {Curves[i]["f3"](u[j - 1],t[j + 1],u[j]) : j in [2..(m - 2)]}
                                join {Curves[i]["f3"](u[m - 2],t[m],    r)});
  end if;
end for;

// Weil restriction

WeilRestriction := function(I)
  t0 := Cputime();
  J := &+[ideal<S1|Coefficients(phi(f))> : f in Basis(I)];
  if IsVerbose("User1") then print "Weil restriction time:",Cputime(t0); end if;
  return J;
end function;

// Point decomposition

ECDLPDecompose := function(E,Q : Al := "All")
  if IsVerbose("User1") then print "Decomposing",Q; end if;
  if Order(Q) ne E["order"] then return []; end if;

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
    if IsVerbose("User1") then print "Batch decomposition time:",Cputime(t0); end if;
  end if;

  if IsVerbose("User1") then print "Rewriting variables"; end if;
  if not elim then
    if IsVerbose("User1") then print "  ... skipped"; end if;
    Irewritten := E["Isummation"] + Icondition;
  else
    case m:
      when 2:
        I := Ideal(Semaev3(E,t[1],t[2],r));
      when 3:
        I := Ideal(Semaev4(E,t[1],t[2],t[3],r));
      when 4:
        I := Ideal(Semaev5(E,t[1],t[2],t[3],t[4],r));
      when 5:
        I := Ideal(Semaev6(E,t[1],t[2],t[3],t[4],t[5],r));
      else
        I := E["Isummation"];
    end case;
    b := GetVerbose("Faugere"); SetVerbose("Faugere",GetVerbose("User2")*2);
    Irewritten := EliminationIdeal(I + Icondition + E["Iauxiliary"],Seqset(s));
    SetVerbose("Faugere",0);
  end if;
  if IX then Irewritten +:= E["Iauxiliary"]; end if;

  Jp := WeilRestriction(Irewritten) + E["Jcondition"];
  t0 := Cputime();
  Zp := CoreVariety(J,Jp : Al := Al);
  if IsVerbose("User1") then print "Point decomposition time:",Cputime(t0); end if;

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

// Sign of point

SignOfPoint := function(E,Q)
  f := func<t|ind((t[1] - t[2])/t[3])>;
  return forall(t){P : P in E["VtoFB"](E["FBtoV"](Q)) | f(P) le f(Q)} select -1 else 1;
end function;

// Relation collection

CollectRelations := procedure(~M,E,Qs)
  for Ps in Qs do
    i := IsEmpty(M) select 1 else M[#M][1] + 1;
    M cat:= [<i,ind(E["FBtoV"](P)) + 1,SignOfPoint(E,P)> : P in Ps];
  end for;
end procedure;

// Experiments

for point := 1 to 1 do
  for E in Curves do
    print ""; print "Working on",E["form"],E["curve"];

    SetVerbose("User1",true);
    SetVerbose("User2",true);
    print "Point A",point;
    repeat
      Ps := [RandomFB(E) : i in [1..m]];
      Qs := ECDLPDecompose(E,&+Ps);
    until not IsEmpty(Qs);
    M := []; CollectRelations(~M,E,Qs);
    if q^l lt SomethingBIG then
      M := SparseMatrix(Integers(),M[#M][1],q^l,M);
      print M,"Rank of relation matrix:",Rank(M);
    else
      print "Number of relations:",#M;
    end if;

    SetVerbose("User1",false);
    SetVerbose("User2",false);
    print "Point B",point;
    M := [];
    t0 := Cputime();
    for trial := 1 to ntrials do
      CollectRelations(~M,E,ECDLPDecompose(E,Random(E["order"])*E["P"] : Al := Al));
    end for;
    if not IsEmpty(M) then
      if q^l lt SomethingBIG then
        M := SparseMatrix(Integers(),M[#M][1],q^l,M);
        print M,"Average rank:",Rank(M)/ntrials;
        print "Rank per second:",Rank(M)/Cputime(t0);
      else
        print "Average #relations:",#M/ntrials;
        print "Relations per second:",#M/Cputime(t0);
      end if;
    end if;
  end for;
  print "Finished Point",point;
end for;

