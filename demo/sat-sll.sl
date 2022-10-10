data node {
  node next;
}.


pred sll<self,n> == emp & self=null & n=0
  or exists u, k: self::node<u> * sll(u,k) & n=k+1.


checksat[unsat] sll(x, n) & n<0.

checksat[sat] sll(x, n) & n=1.

