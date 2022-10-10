
ddata node {
 node next;
}.

pred ll<r,l> == emp & r=l
  or (exists n: r::node<n> * ll(n,l)  &  r != l).


  checksat[unsat] x::node<null> * y::node<n> & x=y.
