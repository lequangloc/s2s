data node {
     node next;
}.


pred ls<x,i> == emp & x = null & i=0
  or exists u,i1: x::node<u> * ls(u,i1) & i=i1+1.

pred ell<self,n> == emp & self=null & n=0
     or exists q,p: self::node<q> * q::node<p> * ell(p,n-2)
     .
