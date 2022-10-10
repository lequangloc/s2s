
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x35,x33) * x33::RefSll_t<next = x35> * ls(x31,x29) * x29::RefSll_t<next = x31> * ls(x27,x25) * x25::RefSll_t<next = x27> * ls(x23,x21) * x21::RefSll_t<next = x23> * ls(x19,x17) * x17::RefSll_t<next = x19> * ls(x15,x13) * x13::RefSll_t<next = x15> * ls(x11,x9) * x9::RefSll_t<next = x11> * ls(x7,x5) * x5::RefSll_t<next = x7> * ls(x3,x1) * x1::RefSll_t<next = x3> & null = null & null != x1 & null != x2 & null != x3 & x1 != x2 & x2 != x3 & null != x5 & null != x6 & null != x7 & x5 != x6 & x6 != x7 & null != x9 & null != x10 & null != x11 & x9 != x10 & x10 != x11 & null != x13 & null != x14 & null != x15 & x13 != x14 & x14 != x15 & null != x17 & null != x18 & null != x19 & x17 != x18 & x18 != x19 & null != x21 & null != x22 & null != x23 & x21 != x22 & x22 != x23 & null != x25 & null != x26 & null != x27 & x25 != x26 & x26 != x27 & null != x29 & null != x30 & null != x31 & x29 != x30 & x30 != x31 & null != x33 & null != x34 & null != x35 & x33 != x34 & x34 != x35
         |- ls(x36,x33) * x33::RefSll_t<next = x36> * ls(x32,x29) * x29::RefSll_t<next = x32> * ls(x28,x25) * x25::RefSll_t<next = x28> * ls(x24,x21) * x21::RefSll_t<next = x24> * ls(x20,x17) * x17::RefSll_t<next = x20> * ls(x16,x13) * x13::RefSll_t<next = x16> * ls(x12,x9) * x9::RefSll_t<next = x12> * ls(x8,x5) * x5::RefSll_t<next = x8> * ls(x4,x1) * x1::RefSll_t<next = x4>.
