ddata node {
     node next;
}.


pred ls<x,i> == emp & x = null & i=0
  or exists u,i1: x::node<u> * ls(u,i1) & i=i1+1.

pred lseg<x,p> == emp & x = p
  or exists u: x::node<u> * lseg(u,p).

pred ell<self,n> == emp & self=null & n=0
     or exists q,p: self::node<q> * q::node<p> * ell(p,n-2)
     .

checksat[sat] ls(x, i) & i=2.

checksat[unsat] ls(x, i) & i<0.
/*

checksat[sat] ls(x, i).

checksat[unsat] ls(x, i) & i<0.

checksat[unsat] (exists i: ls(x, i) & i<0).

checksat[unsat] (exists k: ell(x, i) & i=2*k + 1).
*/