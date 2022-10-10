
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x23,x21) * x21::RefSll_t<next = x23> * ls(x19,x17) * x17::RefSll_t<next = x19> * ls(x15,x13) * x13::RefSll_t<next = x15> * ls(x11,x9) * x9::RefSll_t<next = x11> * ls(x7,x5) * x5::RefSll_t<next = x7> * ls(x3,x1) * x1::RefSll_t<next = x3> & null = null & null != x1 & null != x2 & null != x3 & x1 != x2 & x2 != x3 & null != x5 & null != x6 & null != x7 & x5 != x6 & x6 != x7 & null != x9 & null != x10 & null != x11 & x9 != x10 & x10 != x11 & null != x13 & null != x14 & null != x15 & x13 != x14 & x14 != x15 & null != x17 & null != x18 & null != x19 & x17 != x18 & x18 != x19 & null != x21 & null != x22 & null != x23 & x21 != x22 & x22 != x23
         |- ls(x24,x21) * x21::RefSll_t<next = x24> * ls(x20,x17) * x17::RefSll_t<next = x20> * ls(x16,x13) * x13::RefSll_t<next = x16> * ls(x12,x9) * x9::RefSll_t<next = x12> * ls(x8,x5) * x5::RefSll_t<next = x8> * ls(x4,x1) * x1::RefSll_t<next = x4>.

