data node {
  node left;
  node right;
}.

pred Q<x,y, n> == exists y1: x::node<null,y1> & y=null & x!=null & n=1
  or exists x1,y1: y::node<x1,y1> * Q(x,y1,n-2) & y!=null.


checksat[unsat] Q(x,y, n1) & n1=2*k.
