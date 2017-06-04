R<C0,C1,X1,Y1,X2,Y2,C,D,Y> := PolynomialRing(Rationals(),9);

Z  := C^2*(1 - (D*X1*X2*Y1*Y2)^2);

X3 := (X1*Y2 + X2*Y1)*(1 - D*X1*X2*Y1*Y2);
Y3 := (Y1*Y2 - X2*X1)*(1 + D*X1*X2*Y1*Y2);

X4 := (X1*Y2 - X2*Y1)*(1 + D*X1*X2*Y1*Y2);
Y4 := (Y1*Y2 + X2*X1)*(1 - D*X1*X2*Y1*Y2);

e1 := X1^2 + Y1^2 - (1 + D*X1^2*Y1^2);
e2 := X2^2 + Y2^2 - (1 + D*X2^2*Y2^2);

c0 := Y3 * Y4 - Z^2*C0;
c1 := Y3 + Y4 + Z  *C1;

I0 := Ideal([e1,e2,c0]); J0 := EliminationIdeal(I0,{Y1,Y2,C,D,C0}); G0 := Coefficients(Basis(J0)[1],C0);
I1 := Ideal([e1,e2,c1]); J1 := EliminationIdeal(I1,{Y1,Y2,C,D,C1}); G1 := Coefficients(Basis(J1)[1],C1);

g3 := G0[1]*G1[2] + G0[2]*G1[1]*Y - G0[2]*G1[2]*Y^2;

S<y1,y2,y3,c,d> := PolynomialRing(Rationals(),5);
phi := hom<R->S|[0,0,0,y1,0,y2,c,d,y3]>;
f3 := Factorization(phi(g3))[4][1];
