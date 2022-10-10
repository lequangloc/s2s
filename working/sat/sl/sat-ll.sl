data node {
  node next;
}.

/*
pred lseg<x,p,i> == emp & x = p & i=0
  or exists u: x::node<u> * lseg(u,p,i-1) & x!= p.
*/


pred ls<x> == emp & x = null
  or exists u: x::node<u> * ls(u).


pred ls1<self,i> == emp & self = null & i=0
  or exists u: self::node<u> * ls1(u,i-1).


//checksat[sat] ls(x) .

checksat[sat] ls1(x, n) & n>0.

checksat[unsat] ls1(x, n) & n<0.

