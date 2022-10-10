ddata node {
  node next;
}.


pred ls<x> == emp & x = null
  or exists u: x::node<u> * ls(u).

pred lseg<x,p> == emp & x = p
  or exists u: x::node<u> * lseg(u,p) & x!=p.

//3
checkent[invalid] ls(x) & x!=null |- exists u2: x::node<u2>.

/*

//1. LHS = false. To replace each predicate occurence by its base pair for SAT checking
checkent[valid] x::node<u> * ls(x) |- exists u2: x::node<u2>.

//2a. invalid as recursive case: LHS nonempty, RHS is empty heap
checkent[invalid] ls(x) & x!=null |- exists u2: x::node<u2>.


//2b.
checkent[invalid] ls(x) & x=null |- exists u2:  x::node<u2>.

//2c.
checkent[invalid] ls(x) |- exists u2: x::node<u2>.

//2d.
checkent[valid] ls(x) & x=null & x=x2|- x2=null.

*/
