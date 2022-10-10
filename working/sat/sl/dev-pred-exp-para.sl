data node {
  node next;
}.

/*
pred ls<i> == emp & self = null & i=0
  or exists u: self::node<u> * u::ls<i-1>.
*/

pred ls<x,i> == emp & x = null & i=0
  or exists u: x::node<u> * ls(u,i-1).
