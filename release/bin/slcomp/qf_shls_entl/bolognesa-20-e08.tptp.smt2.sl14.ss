
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x16::RefSll_t<next = x19> * x17::RefSll_t<next = x13> * x12::RefSll_t<next = x8> * x20::RefSll_t<next = x1> * ls(x2,x8) * ls(x4,x8) * x18::RefSll_t<next = x12> * ls(x5,x15) * ls(x14,x20) * ls(x15,x6) * ls(x13,x7) * x19::RefSll_t<next = x1> * x1::RefSll_t<next = x12> * x8::RefSll_t<next = x7> * x9::RefSll_t<next = x11> * x7::RefSll_t<next = x10> * x3::RefSll_t<next = x7> * x6::RefSll_t<next = x3> * ls(x11,x17) * x10::RefSll_t<next = x17> & null = null
         |- ls(x10,x17) * ls(x14,x20) * ls(x16,x19) * ls(x5,x6) * ls(x2,x8) * ls(x18,x12) * ls(x20,x1) * ls(x6,x3) * ls(x3,x7) * ls(x9,x11) * ls(x19,x8) * ls(x4,x7) * ls(x11,x10).

