
data Sll_t {
  Sll_t next;
}.

pred ls<x,out:Sll_t> ==
emp & x = out
or (exists u: x::Sll_t<next = u> * ls(u,out) & x != out).

checksat[sat] ls(x13,x10) * ls(x16,x10) * ls(x10,x19) * ls(x18,x14) * ls(x1,x20) * ls(x14,x3) * ls(x15,x14) * ls(x17,x10) * ls(x7,x10) * ls(x3,x20) * ls(x11,x2) * ls(x11,x8) * ls(x6,x2) * emp & null = null & x6 != x13 & x11 != x14 & x3 != x7 & x7 != x10 & x7 != x14 //& x9 != x11
 & x17 != x19 //& x12 != x18 & x12 != x17
 & x2 != x11 & x2 != x19 & x2 != x17 & x14 != x16 & x1 != x3 //& x4 != x17
 & x10 != x19 & x10 != x17 & x10 != x15 & x13 != x18 & x13 != x17 //& x5 != x7 & x5 != x20
         .

