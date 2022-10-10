
data Sll_t {
  Sll_t next;
}.

pred ls<x,out:Sll_t> ==
  x = out
or (exists u: x::Sll_t<next = u> * ls(u,out) & x != out).


checksat[sat] ls(x10,x1) * ls(x13,x4) * ls(x16,x18) * ls(x18,x12) * ls(x4,x20) * ls(x4,x3) * ls(x20,x11) * ls(x20,x8) * ls(x14,x11) * ls(x17,x15) * ls(x17,x18) * ls(x2,x14) * ls(x7,x12) * ls(x7,x3) * ls(x11,x20) * emp & null = null & x11 != x13 & x11 != x12 & x3 != x7 & x3 != x12 & x7 != x10 & x7 != x14 & x9 != x18 & x9 != x16 & x2 != x6 & x2 != x10 & x15 != x16 & x15 != x19 & x14 != x16 & x14 != x20 & x8 != x12 & x8 != x14 & x1 != x13 & x1 != x15 & x1 != x5 & x4 != x11 & x4 != x5 & x10 != x18 & x10 != x19 & x10 != x15 & x5 != x9 & x5 != x15
    .


/*
checksat //ls(x10,x1) *
 ls(x13,x4) * ls(x16,x18) * ls(x18,x12) * ls(x4,x20) * ls(x4,x3) * ls(x20,x11) * ls(x20,x8) * ls(x14,x11) * ls(x17,x15) * ls(x17,x18) * ls(x2,x14) * ls(x7,x12) * ls(x7,x3) * ls(x11,x20) * emp & null = null & x11 != x13 & x11 != x12 & x3 != x7 & x3 != x12 & x7 != x10 & x7 != x14
 //& x9 != x18 & x9 != x16 
& x2 != x6 & x2 != x10 
& x15 != x16 & x15 != x19 & x14 != x16 & x14 != x20 & x8 != x12 & x8 != x14 & x1 != x13 & x1 != x15
 // & x1 != x5 
& x4 != x11
 //& x4 != x5
 & x10 != x18 & x10 != x19 & x10 != x15
 //& x5 != x9 & x5 != x15
         .
*/
