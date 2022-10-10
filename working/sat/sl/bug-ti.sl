data GTyp {
  GTyp f0;
  GTyp f1;
}.

pred R<x> == P(x) & null != x.


pred Q<x,y> ==
 (exists d,c: x::GTyp<d, c> * P(d) & null = y & null != x)
or (exists d,c: y::GTyp<d, c> * Q(x,c) & null != y).

pred P<x> == emp &  null = x
or Q(x, x) & null != x.

//checksat R(x0).

checksat P(x0) & null != x0.

//expect Unsat.


