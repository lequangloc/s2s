// the singleton heap predicate which models a data structure
data node {
    node next;
    node prev;
}.

// inductive heap predicates which model the data structures' shapes
//pred dll<p,tl,n,l> == emp & self=n & tl=p & l=0
//    or (exists x: self::node<x,p> * x::dll<self,tl,n,l-1>).

pred dll<x, p,tl,n> == emp & x=n & tl=p
    or (exists x1: x::node<x1,p> * dll(x1,x,tl,n)).

/*
   emp & x=n & tl=p
\/ x::node<x1,p> & x1=n & tl=x
\/ x::node<x1,p> * x1::node<x2,x> & x2=n & tl=x1
*/

checksat[sat] dll(x, p,tl,n).


