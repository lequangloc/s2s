// the singleton heap predicate which models a data structure
data node {
    node next;
    node prev;
}.


pred Q<x,y> == P1(x) * P2(y).

/*
pred Q< x,y> == P1(x)_0^0 * P2(y)_0^1 & true
 inv exists idx_27: 0=idx_27 && y>=0 && x>=0.

*/

pred P1<x> == x=0
  or exists x1: P1(x1) & x=x1+2.

pred P2<y> == y=0
  or exists y1: P2(y1) & y=y1+3.


checksat[sat] Q(x,y).

/*
ERROR: at _-1:0_-1:0
Message: Cpure.type_decomp: no separation on pointer and arith
Fatal error: exception Failure("Cpure.type_decomp: no separation on pointer and arith")

*/
