
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent emp & null = null & null != x1 & null != x2 & x1 != x2 & null != x3 & null != x4 & x3 != x4 & null != x5 & null != x6 & x5 != x6 & null != x7 & null != x8 & x7 != x8 & null != x9 & null != x10 & x9 != x10 & null != x11 & null != x12 & x11 != x12 & null != x13 & null != x14 & x13 != x14 & null != x15 & null != x16 & x15 != x16 & null != x17 & null != x18 & x17 != x18 & null != x19 & null != x20 & x19 != x20
         |- emp.

