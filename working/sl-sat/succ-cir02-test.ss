
ddata RefGTyp {
  RefGTyp f0;
  RefGTyp f1;
}.

pred one<x:RefGTyp> ==
emp & null != x.

pred Q<y1:RefGTyp,y2:RefGTyp> ==
 zero(y1) * zero(y2)
or (exists x1,x2: succ2circuit(x1,x2,y1,y2) * Q(x1,x2)).

pred P<x1:RefGTyp,x2:RefGTyp> ==
one(x1) * one(x2) * Q(x1,x2).

pred zero<x:RefGTyp> ==
emp & null = x.

pred succ2circuit<x1:RefGTyp,x2:RefGTyp,y1:RefGTyp,y2:RefGTyp> ==
notg(x1,y1) * xorg(x1,x2,y2).

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

checkent[invalid] P(x0,x1)
         |- false.

