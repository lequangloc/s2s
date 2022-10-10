data node {
  node left;
  node right;
}.

pred Q<x,y> == exists y1: x::node<null,y1> & y=null & x!=null
  or exists x1,y1: y::node<x1,y1> * Q(x,y1) & y!=null.


checksat Q(x,y) .

