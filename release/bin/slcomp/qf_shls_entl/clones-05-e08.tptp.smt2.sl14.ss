
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x18,x17) * x19::RefSll_t<next = x18> * x17::RefSll_t<next = x19> * ls(x14,x13) * x15::RefSll_t<next = x14> * x13::RefSll_t<next = x15> * ls(x10,x9) * x11::RefSll_t<next = x10> * x9::RefSll_t<next = x11> * ls(x6,x5) * x7::RefSll_t<next = x6> * x5::RefSll_t<next = x7> * ls(x2,x1) * x3::RefSll_t<next = x2> * x1::RefSll_t<next = x3> & null = null & null != x1 & null != x2 & null != x3 & x1 != x3 & x2 != x3 & null != x5 & null != x6 & null != x7 & x5 != x7 & x6 != x7 & null != x9 & null != x10 & null != x11 & x9 != x11 & x10 != x11 & null != x13 & null != x14 & null != x15 & x13 != x15 & x14 != x15 & null != x17 & null != x18 & null != x19 & x17 != x19 & x18 != x19
         |- x20::RefSll_t<next = x19> * ls(x18,x20) * x19::RefSll_t<next = x18> * x16::RefSll_t<next = x15> * ls(x14,x16) * x15::RefSll_t<next = x14> * x12::RefSll_t<next = x11> * ls(x10,x12) * x11::RefSll_t<next = x10> * x8::RefSll_t<next = x7> * ls(x6,x8) * x7::RefSll_t<next = x6> * x4::RefSll_t<next = x3> * ls(x2,x4) * x3::RefSll_t<next = x2>.

