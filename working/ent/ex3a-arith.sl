data node {
  node next;
}.


pred lsn<x,n> == emp & x = null & n=0
  or exists u: x::node<u> * lsn(u, n-1).

//2b.
checkent[valid] lsn(x,n) & n=1 |- exists u: x::node<u> .


/*
//2b.
checkent[valid] lsn(x,n) & n=1 |- exists u: x::node<u> .

//2c
checkent[valid] lsn(x,n)  & n=0  |- emp & true.
/*
   emp /\ x=null /\ n=0 
\/ x|->_x1 * lln(x1, n-1) & n=0
*/


//2d. OK
checkent[valid] lsn(x,n) & n=1 |-  x::node<null> .

//2a. OK
checkent[valid] lsn(x,n) & n=0 |- emp & x=null.

//2e: OK
checkent[invalid] lsn(x,n) * x2::node<null> & n=0  |- emp & true.

*/

