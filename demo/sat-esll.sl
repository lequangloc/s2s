data node {
  node next;
}.


pred esll<self,n> == emp & self=null & n=0
  or exists r1,r2, k: self::node<r1> * r1::node<r2> * esll(r2,k) & n=k+2.


checksat[unsat] (exists i: esll(x, n) & n=2*i+1 & i>16000).

