
data Sll_t {
  Sll_t next;
}.

pred ls<x, out:Sll_t> == x = out
or (exists u: x::Sll_t<u> * ls(u, out) & x != out).

checksat[unsat] ls(x5,x7) * ls(x2,x5) * ls(x2,x10) * ls(x2,x1) * ls(x9,x1) * ls(x7,x6) * ls(x3,x10) * ls(x6,x9) & x1 != x6 & x1 != x7 & x1 != x10 & x7 != x10 & x2 != x6 & x2 != x3 & x2 != x7 
 & x4!=x8 & x4!=x7 & x4!=x9 & x3!=x8.

