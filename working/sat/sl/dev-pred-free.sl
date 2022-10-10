data node {
  node next;
}.


pred ls<x,i> == emp & x = null & i=0
  or exists u,i1: x::node<u> * ls(u,i1) & i1=i-1.
