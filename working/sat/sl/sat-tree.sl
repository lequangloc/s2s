data node {
  node left;
  node right;
}.

pred bt<x> == emp & x = null
  or exists l,r: x::node<l,r> * bt(l) * bt(r).


checksat bt(x) .

