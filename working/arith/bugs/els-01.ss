data node {
     node next;
}.



pred ell<self,n> == emp & self=null & n=0
     or exists q,p: self::node<q> * q::node<p> * ell(p,n-2)
     .


checksat[sat] ell(x, i) & i=320000.

