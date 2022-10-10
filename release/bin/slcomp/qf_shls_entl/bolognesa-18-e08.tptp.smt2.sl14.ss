
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x1::RefSll_t<next = x5> * ls(x3,x17) * x16::RefSll_t<next = x10> * x6::RefSll_t<next = x10> * ls(x12,x11) * x10::RefSll_t<next = x11> * ls(x14,x8) * x18::RefSll_t<next = x10> * x7::RefSll_t<next = x14> * x2::RefSll_t<next = x18> * x8::RefSll_t<next = x7> * ls(x13,x5) * x15::RefSll_t<next = x4> * ls(x17,x5) * x5::RefSll_t<next = x14> * ls(x11,x10) * x9::RefSll_t<next = x17> * ls(x4,x5) & null = null
         |- ls(x15,x4) * ls(x13,x5) * ls(x7,x14) * ls(x6,x10) * ls(x3,x17) * ls(x2,x18) * ls(x12,x10) * ls(x18,x10) * ls(x4,x5) * ls(x16,x11) * ls(x9,x5) * ls(x1,x7).

