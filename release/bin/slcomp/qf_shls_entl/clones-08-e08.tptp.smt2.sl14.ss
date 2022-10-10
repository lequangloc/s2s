
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x30,x29) * x31::RefSll_t<next = x30> * x29::RefSll_t<next = x31> * ls(x26,x25) * x27::RefSll_t<next = x26> * x25::RefSll_t<next = x27> * ls(x22,x21) * x23::RefSll_t<next = x22> * x21::RefSll_t<next = x23> * ls(x18,x17) * x19::RefSll_t<next = x18> * x17::RefSll_t<next = x19> * ls(x14,x13) * x15::RefSll_t<next = x14> * x13::RefSll_t<next = x15> * ls(x10,x9) * x11::RefSll_t<next = x10> * x9::RefSll_t<next = x11> * ls(x6,x5) * x7::RefSll_t<next = x6> * x5::RefSll_t<next = x7> * ls(x2,x1) * x3::RefSll_t<next = x2> * x1::RefSll_t<next = x3> & null = null & null != x1 & null != x2 & null != x3 & x1 != x3 & x2 != x3 & null != x5 & null != x6 & null != x7 & x5 != x7 & x6 != x7 & null != x9 & null != x10 & null != x11 & x9 != x11 & x10 != x11 & null != x13 & null != x14 & null != x15 & x13 != x15 & x14 != x15 & null != x17 & null != x18 & null != x19 & x17 != x19 & x18 != x19 & null != x21 & null != x22 & null != x23 & x21 != x23 & x22 != x23 & null != x25 & null != x26 & null != x27 & x25 != x27 & x26 != x27 & null != x29 & null != x30 & null != x31 & x29 != x31 & x30 != x31
         |- x32::RefSll_t<next = x31> * ls(x30,x32) * x31::RefSll_t<next = x30> * x28::RefSll_t<next = x27> * ls(x26,x28) * x27::RefSll_t<next = x26> * x24::RefSll_t<next = x23> * ls(x22,x24) * x23::RefSll_t<next = x22> * x20::RefSll_t<next = x19> * ls(x18,x20) * x19::RefSll_t<next = x18> * x16::RefSll_t<next = x15> * ls(x14,x16) * x15::RefSll_t<next = x14> * x12::RefSll_t<next = x11> * ls(x10,x12) * x11::RefSll_t<next = x10> * x8::RefSll_t<next = x7> * ls(x6,x8) * x7::RefSll_t<next = x6> * x4::RefSll_t<next = x3> * ls(x2,x4) * x3::RefSll_t<next = x2>.

