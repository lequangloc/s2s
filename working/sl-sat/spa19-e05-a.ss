
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
  or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checksat ls(x5:RefSll_t,x12:RefSll_t) * ls(x5:RefSll_t,x16:RefSll_t) * ls(x5:RefSll_t,x7:RefSll_t) * ls(x5:RefSll_t,x8:RefSll_t) * ls(x19:RefSll_t,x2:RefSll_t) * ls(x19:RefSll_t,x13:RefSll_t) * ls(x16:RefSll_t,x12:RefSll_t) * ls(x13:RefSll_t,x14:RefSll_t) * ls(x10:RefSll_t,x1:RefSll_t) * ls(x1:RefSll_t,x2:RefSll_t) * ls(x1:RefSll_t,x17:RefSll_t) * ls(x8:RefSll_t,x17:RefSll_t) * ls(x15:RefSll_t,x7:RefSll_t) * ls(x14:RefSll_t,x19:RefSll_t) * ls(x12:RefSll_t,x16:RefSll_t) * ls(x12:RefSll_t,x9:RefSll_t) * ls(x3:RefSll_t,x4:RefSll_t) * ls(x3:RefSll_t,x8:RefSll_t) * ls(x11:RefSll_t,x19:RefSll_t) * ls(x11:RefSll_t,x4:RefSll_t) * ls(x6:RefSll_t,x3:RefSll_t) & null = null & x6:RefSll_t != x15:RefSll_t & x3:RefSll_t != x14:RefSll_t & x7:RefSll_t != x19:RefSll_t & x7:RefSll_t != x13:RefSll_t & x9:RefSll_t != x11:RefSll_t & x12:RefSll_t != x17:RefSll_t & x2:RefSll_t != x6:RefSll_t & x2:RefSll_t != x16:RefSll_t & x2:RefSll_t != x15:RefSll_t & x2:RefSll_t != x14:RefSll_t & x8:RefSll_t != x13:RefSll_t & x1:RefSll_t != x18:RefSll_t & x1:RefSll_t != x12:RefSll_t & x4:RefSll_t != x8:RefSll_t & x4:RefSll_t != x10:RefSll_t & x13:RefSll_t != x15:RefSll_t.

