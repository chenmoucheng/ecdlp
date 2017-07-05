/*
 * Solving the core of an ideal
 */

// Distribution of degrees of polynomials in set F

Degrees := function(F)
  D := [];
  for f in F do
    d := TotalDegree(f);
    if d eq 0 then continue; end if;
    D[d] := IsDefined(D,d) select D[d] + 1 else 1;
  end for;
  for d := 1 to #D do
    D[d] := IsDefined(D,d) select D[d]     else 0;
  end for;

  return D;
end function;

// Whether variable v is in support of polynomial f

InSupport := function(v,f)
  return Degree(f,v) gt 0;
end function;

// Gap degrees of polynomial set F

GapDegrees := function(L,...)
  F := L[1];
  if Seqset(F) eq {1} then return []; end if;
  G := IsDefined(L,2) select L[2] else GroebnerBasis(Ideal(F));
  d := Maximum({TotalDegree(f) : f in F});
  H := [[] : i in [1..(d - 1)]];
  t0 := Cputime();
  H[d] := GroebnerBasis(F,d);
  print "Groebner basis time:",Cputime(t0),d,#H[d],"=",Degrees(H[d]);
  repeat
    d +:= 1;
    t0 := Cputime();
    H[d] := GroebnerBasis(F,d);
    print "Groebner basis time:",Cputime(t0),d,#H[d],"=",Degrees(H[d]);
    F_ := {f : f in H[d] | TotalDegree(f) lt d and NormalForm(f,H[d - 1]) ne 0};
    if not IsEmpty(F_) then print "  Gap degree and sizes:",d,#F_,"=",Degrees(F_); end if;
  until #G eq #H[d] and Seqset(G) eq Seqset(H[d]);

  return H;
end function;

// Ideal of singleton variety v

IdealOfSingleton := function(R,v)
  assert BaseRing(R) eq Parent(v[1]) and Rank(R) eq #v;
  return Ideal({R.i - v[i] : i in [1..Rank(R)]});
end function;

// Ideals of singletons of zero-dimensional variety V

IdealsOfSingletons := function(R,V)
  return [IdealOfSingleton(R,v) : v in V];
end function;

// Ideal of zero-dimensional variety V

IdealOfVariety := function(R,V)
  I := ideal<R|1>;
  for v in V do
    I *:= IdealOfSingleton(R,v);
  end for;
  return I;
end function;

// Variety size of ideal I over its base field

VarietySizeOverCoefficientField := function(I)
  R := Generic(I);
  S := PolynomialRing(BaseRing(R),Rank(R));
  phi := hom<R->S|[S.i : i in [1..Rank(S)]]>;
  J := Ideal({phi(f) : f in Basis(I)}) + Ideal({S.i^#BaseRing(S) - S.i : i in [1..Rank(S)]});
  return VarietySizeOverAlgebraicClosure(J);
end function;

// Variety of zero-dimensional ideal I using SAT solver

SATVariety := function(I : Bound := 0,Verbose := false)
  V := []; L := [];
  if Seqset(Basis(I)) ne {1} then
    if Bound eq 0 then Bound := VarietySizeOverCoefficientField(I); end if;
    t0 := Cputime();
    for i := 1 to Bound do
      sat,sol,L := SAT(Basis(I) : Cpulim := 200,Exclude := V,Litlim := 5,Termlim := 100,Verbose := Verbose);
      if sat then
        Append(~V,sol);
        if i eq Bound then
          print "SAT time:",Cputime(t0),i,#L;
        end if;
      else
        print "SAT time:",Cputime(t0),i - 1,Bound,#L;
        break;
      end if;
    end for;
  end if;

  return V,L;
end function;

// Core ideal after substituting constant and ignoring unassigned variables

CoreIdeal := function(I)
  R := Generic(I);
  F := {f : f in Basis(I) | IsUnivariate(f)}; F_ := Seqset(Basis(I)) diff F;
  U := [R.i : i in [1..Rank(R)] | forall(t){f : f in F  | not InSupport(R.i,f)}
                              and exists(t){f : f in F_ |     InSupport(R.i,f)}];
  S := #k eq 2 select BooleanPolynomialRing(#U,"grevlex")
       else PolynomialRing(k,#U,"grevlex") where k is BaseRing(R);
  V := [S|];
  for i := 1 to Rank(R) do
    if R.i in U then
      Append(~V,S.Index(U,R.i));
    else
      x := exists(g){UnivariatePolynomial(f) : f in F | InSupport(R.i,f)}
           select Random(Roots(g))[1] else Random(BaseRing(R));
      Append(~V,x);
    end if;
  end for;
  phiRS := hom<R->S|V>;
  phiSR := hom<S->R|U>;
  J := Ideal({g : f in Basis(I) | g ne 0 where g is phiRS(f)});

  return J,phiSR;
end function;

// Variety of zero-dimensional ideal I with core ideal Ic

CoreVariety := function(I,Ic : Al := "All",Verbose := false)
  Jc,phi := CoreIdeal(Ic);
  Rc := Generic(Jc);
  b := GetVerbose("Faugere");
  case Al:
    when "All":
      Ic := Ideal(Basis(Jc));
      SetVerbose("Faugere",Verbose select 2 else 0);
      Groebner(Ic);
      SetVerbose("Faugere",0);
      Vc := Variety(Ic);
      Hc := GapDegrees(Basis(Jc),Basis(Ic));
      /*
      _ := SATVariety(Ic : Bound := 1);
      _ := SATVariety(Jc : Bound := 1);
      if #Hc ge 2 then _ := SATVariety(Ideal(Hc[#Hc - 1]) : Bound := 1); end if;
      _ := SATVariety(Ic);
      _ := SATVariety(Jc);
      if #Hc ge 2 then V := SATVariety(Ideal(Hc[#Hc - 1])); end if;
      */
      // P := IdealOfVariety(Rc,V); Groebner(P);
      // assert Seqset(Basis(Ic)) eq Seqset(Basis(P));
    when "SAGB":
      _,L := SATVariety(Ideal(RandomSubset(F,#F - 0)) : Bound := 1,Verbose := true) where F is Seqset(Basis(Jc));
      SetVerbose("Faugere",Verbose select 2 else 0);
      Vc := Variety(Jc + ideal<Rc|L>);
      SetVerbose("Faugere",0);
    when "SAT":
      SetVerbose("Faugere",Verbose select 2 else 0);
      Vc := SATVariety(Jc);
      SetVerbose("Faugere",0);
    else
      SetVerbose("Faugere",Verbose select 2 else 0);
      Vc := Variety(Jc);
      SetVerbose("Faugere",0);
  end case;
  V := [];
  for J in IdealsOfSingletons(Rc,Vc) do
    v := Variety(I + Ideal({phi(f) : f in Basis(J)}));
    if not IsEmpty(v) then
      V cat:= v;
    else
      print "Extraneous root found";
    end if;
  end for;
  SetVerbose("Faugere",b);

  return V;
end function;

