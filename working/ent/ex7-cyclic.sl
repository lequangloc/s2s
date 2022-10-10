
data node {
  node next;
}.

data node2 {
  node2 left;
  node2 right;
}.


pred ls<x> == emp & x = null
  or exists u: x::node<u> * ls(u).

pred ls1<x> == emp & x = null
  or exists u: x::node<u> * ls1(u).

pred ls2<x> == emp & x = null
  or exists u,u2: x::node<u> * u::node<u2> * ls2(u2).

pred lseg<x,p> == emp & x = p
  or exists u: x::node<u> * lseg(u,p) & x!=p.


//5. not link at the first if the global soundness condition does
//  not hold
//checkent[valid] x::node<u> * ls1(u) |- ls(x) .
checkent[invalid] ls(x) |- ls2(x) .


/*

//0. implicit vars
checkent[valid]  exists u: x::node<u> * u::node<null> |- exists u1: x::node<u1> * u1::node<null>.

//0b. update subterm to capture implicit qvars
checkent[valid] ls(x) & x!=null |- exists u: x::node<u> * ls(u) .

//1
checkent[valid] ls1(x) |- ls(x) .

//2
checkent[valid] lseg(x, y) * ls(y) |- ls(x) .


//3
checkent[valid] lseg(x, y) * y::node<null> & x!=y  |- ls(x) .

//4a
checkent[valid] ls2(x) |- ls(x) .

//4b
checkent[invalid] ls(x) |- ls2(x) .


//5. not link at the first if the global soundness condition does
//  not hold
checkent[valid] x::node<u> * ls1(u) |- ls(x) .


//6a
checkent[invalid] lseg(x,y) * lseg(y, z) |- lseg(x, z) .


*/