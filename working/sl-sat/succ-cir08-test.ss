
ddata RefGTyp {
  RefGTyp f0;
  RefGTyp f1;
}.

pred one<x:RefGTyp> ==
emp & null != x.

pred Q<y1:RefGTyp,y2:RefGTyp,y3:RefGTyp,y4:RefGTyp,y5:RefGTyp,y6:RefGTyp,y7:RefGTyp,y8:RefGTyp> ==
 zero(y1) * zero(y2) * zero(y3) * zero(y4) * zero(y5) * zero(y6) * zero(y7) * zero(y8)
or (exists x1,x2,x3,x4,x5,x6,x7,x8: succ8circuit(x1,x2,x3,x4,x5,x6,x7,x8,y1,y2,y3,y4,y5,y6,y7,y8) * Q(x1,x2,x3,x4,x5,x6,x7,x8)).

pred P<x1:RefGTyp,x2:RefGTyp,x3:RefGTyp,x4:RefGTyp,x5:RefGTyp,x6:RefGTyp,x7:RefGTyp,x8:RefGTyp> ==
one(x1) * one(x2) * one(x3) * one(x4) * one(x5) * one(x6) * one(x7) * one(x8) * Q(x1,x2,x3,x4,x5,x6,x7,x8).

pred zero<x:RefGTyp> ==
emp & null = x.

pred succ8circuit<x1:RefGTyp,x2:RefGTyp,x3:RefGTyp,x4:RefGTyp,x5:RefGTyp,x6:RefGTyp,x7:RefGTyp,x8:RefGTyp,y1:RefGTyp,y2:RefGTyp,y3:RefGTyp,y4:RefGTyp,y5:RefGTyp,y6:RefGTyp,y7:RefGTyp,y8:RefGTyp> ==
(exists z3,z4,z5,z6,z7,z8: notg(x1,y1) * xorg(x1,x2,y2) * andg(x1,x2,z3) * xorg(z3,x3,y3) * andg(z3,x3,z4) * xorg(x4,y4,z4) * andg(z4,x4,z5) * xorg(x5,y5,z5) * andg(z5,x5,z6) * xorg(x6,y6,z6) * andg(z6,x6,z7) * xorg(x7,y7,z7) * andg(z7,x7,z8) * xorg(x8,y8,z8)).

pred notg<x:RefGTyp,y:RefGTyp> ==
 zero(x) * one(y)
or one(x) * zero(y).

pred xorg<x:RefGTyp,y:RefGTyp,z:RefGTyp> ==
 zero(x) * zero(y) * zero(z)
or zero(x) * one(y) * one(z)
or one(x) * zero(y) * one(z)
or one(x) * one(y) * zero(z).

pred andg<x:RefGTyp,y:RefGTyp,z:RefGTyp> ==
 zero(x) * zero(z)
or zero(y) * zero(z)
or one(x) * one(y) * one(z).

   checkent[invalid] P(x0,x1,x2,x3,x4,x5,x6,x7)
      |- false.

