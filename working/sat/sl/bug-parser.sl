data GTyp {
  GTyp f0;
  GTyp f1;
}.

pred R<x> == P(x) & null != x.

pred P<x:GTyp> == emp &  null = x
or Q(x, x) & null != x.

pred Q<x,y> ==
 (exists d,c: x::GTyp<d, c> * P(d) & null = y & null != x)
or (exists d,c: y::GTyp<d, c> * Q(x,c) & null != y).

//checksat R(x0).

checksat P(x0) & null != x0.

//expect Unsat.


/*
WARNING : parsing problem Q is not
 a relation nor a heap predicate

Fatal error: exception Failure("gather_type_info_b_formula: relation Q cannot be found")


*/