data node {
  node next;
}.


pred ls<x,i> == emp & x = null & i=0
  or exists u,i1: x::node<u> * ls(u,i1) & i=i1+2.

pred ls2<x,i> == emp & x = null & i=1
  or exists u,i1: x::node<u> * ls2(u,i1) & i=i1+2.



