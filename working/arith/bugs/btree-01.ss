ddata node {
  node left;
  node right;
}.

pred bt<x, len1> == emp & x = null & len1 = 0
  or exists l,r,n1,n2: x::node<l,r> * bt(l,n1) * bt(r,n2) & len1=n1+n2+1.


checksat[sat] bt(x,n1) & n1=320001.

