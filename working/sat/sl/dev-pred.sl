data node {
  node next;
}.

/*
pred lseg<x,p,i> == emp & x = p & i=0
  or exists u: x::node<u> * lseg(u,p,i-1) & x!= p.
*/

pred ls<x,i> == emp & x = null & i=0
  or exists u,i1: x::node<u> * ls(u,i1) & i1=i-1.

/*
pred ls1<p,i> == emp & self = p & i=0
  or exists u: self::node<u> * u::ls1(p,i-1).
*/

checksat ls(x,n) & n<0 .

