
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checksat ls(x5,x12) * ls(x5,x16) * ls(x5,x7) * ls(x5,x8) * ls(x19,x2) * ls(x19,x13) * ls(x16,x12) * ls(x13,x14) * ls(x10,x1) * ls(x1,x2) * ls(x1,x17) * ls(x8,x17) * ls(x15,x7) * ls(x14,x19) * ls(x12,x16) * ls(x12,x9) * ls(x3,x4) * ls(x3,x8) * ls(x11,x19) * ls(x11,x4) * ls(x6,x3) & null = null & x6 != x15 & x3 != x14 & x7 != x19 & x7 != x13 & x9 != x11 & x12 != x17 & x2 != x6 & x2 != x16 & x2 != x15 & x2 != x14 & x8 != x13 & x1 != x18 & x1 != x12 & x4 != x8 & x4 != x10 & x13 != x15.

