data node {
  node next;
}.

/*
pred lseg<x,p,i> == emp & x = p & i=0
  or exists u: x::node<u> * lseg(u,p,i-1) & x!= p.
*/

//7
checkent[valid] x::node<u> |-  x::node<u2>.


/*
//1
checkent[valid] x>3 |- x>2.

//2
checkent[valid] emp & x>3 |- emp & x>2.

//3
checkent[invalid] emp & x>3 |- emp & x<2.

//4
//checksat[unsat] x::node<u> * x::node<u2>.
checkent[valid] x::node<u> * x::node<u2> |- true.

//5
checkent[invalid] x::node<u> |- true.

//6
//checksat[unsat] exists x, u, u2: x::node<u> * x::node<u2>.
//checkent[invalid] true |- exists x, u, u2: x::node<u> * x::node<u2>.

//8
checkent[valid] x::node<u> |- exists z: x::node<z>.

//9
checkent[invalid] x::node<y> |- x::node<z>.

//10
//need footprint for Elt.eval
checkent[valid] x::node<u> * u::node<null>  |- exists z: x::node<z> * z::node<_> & x!=z.


*/
