data node {
  node l;
  node r;
}.


pred bt<x> == emp & x = null
  or exists l,r: x::node<l,r> * bt(l) * bt(r).



//3
checkent[valid] bt(y) * t::node<null,null> & x!=null & y=x |- exists p,p1: x::node<p,p1> * bt(p) * bt(p1) * bt(t) & t!=null.


/*
//1a
checkent[valid] bt(y) & x!=null & y=x |- exists p,p1: x::node<p,p1> * bt(p) * bt(p1).

//1b
checkent[valid] y::node<null,null> & x!=null & y=x |- bt(x).

//2
checkent[invalid] bt(y) & x!=null & y=x |- exists p: x::node<p,_> * bt(p).

//3a
checksat[sat] (exists l_124,r_125: t::node<l_124,r_125> * bt(l_124) * bt(r_125) * y::node<l_48,r_49> * bt(l_48) * bt(r_49) & t!=null).

*/
