
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x1::RefSll_t<next = x19> * ls(x9,x6) * x17::RefSll_t<next = x3> * ls(x8,x4) * x5::RefSll_t<next = x20> * x4::RefSll_t<next = x8> * x13::RefSll_t<next = x11> * x16::RefSll_t<next = x17> * x3::RefSll_t<next = x11> * x15::RefSll_t<next = x3> * x20::RefSll_t<next = x18> * x18::RefSll_t<next = x12> * ls(x14,x11) * x2::RefSll_t<next = x10> * ls(x7,x10) * x10::RefSll_t<next = x5> * x6::RefSll_t<next = x7> * ls(x12,x19) * ls(x19,x15) * x11::RefSll_t<next = x20> & null = null
         |- ls(x16,x17) * ls(x2,x10) * ls(x1,x19) * ls(x14,x11) * ls(x17,x3) * ls(x4,x8) * ls(x13,x20) * ls(x8,x4) * ls(x9,x11).

