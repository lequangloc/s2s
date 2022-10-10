
data RefGTyp {
  RefGTyp f0;
  RefGTyp f1;
}.

pred one<x:RefGTyp> ==
emp & null != x.

pred Q<y1:RefGTyp,y2:RefGTyp,y3:RefGTyp,y4:RefGTyp> ==
 zero(y1) * zero(y2) * zero(y3) * zero(y4)
or (exists x1,x2,x3,x4: succ4circuit(x1,x2,x3,x4,y1,y2,y3,y4) * Q(x1,x2,x3,x4)).

pred P<x1:RefGTyp,x2:RefGTyp,x3:RefGTyp,x4:RefGTyp> ==
one(x1) * one(x2) * one(x3) * one(x4) * Q(x1,x2,x3,x4).

pred zero<x:RefGTyp> ==
emp & null = x.

pred succ4circuit<x1:RefGTyp,x2:RefGTyp,x3:RefGTyp,x4:RefGTyp,y1:RefGTyp,y2:RefGTyp,y3:RefGTyp,y4:RefGTyp> ==
(exists z3,z4: notg(x1,y1) * xorg(x1,x2,y2) * andg(x1,x2,z3) * xorg(z3,x3,y3) * andg(z3,x3,z4) * xorg(x4,y4,z4)).

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

checksat[sat] P(x0,x1,x2,x3).

