
data GTyp {
  GTyp f0;
  GTyp f1;
}.

pred R<x> == P(x) & null != x.

pred P<x> == emp &  null = x
or Q(x, x) & null != x.

pred Q<x,y> ==
 (exists d,c: x::GTyp<d, c> * P(d) & null = y & null != x)
or (exists d,c: y::GTyp<d, c> * Q(x,c) & null != y)
or (exists d: S(x, y, d) & null != x).

pred S<x,y,z> == (exists c: z::GTyp<c, c> * P(z))
 or x::GTyp<null, null> * Q(x, y).


checksat[unsat] R(x0).


