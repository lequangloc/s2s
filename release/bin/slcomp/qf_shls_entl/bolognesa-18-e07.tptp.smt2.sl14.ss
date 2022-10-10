
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x4,x8) * x9::RefSll_t<next = x13> * x11::RefSll_t<next = x5> * x15::RefSll_t<next = x2> * ls(x12,x9) * ls(x13,x5) * x14::RefSll_t<next = x3> * ls(x5,x13) * x7::RefSll_t<next = x17> * x6::RefSll_t<next = x3> * x18::RefSll_t<next = x7> * x10::RefSll_t<next = x16> * x2::RefSll_t<next = x11> * x16::RefSll_t<next = x3> * ls(x17,x1) * x8::RefSll_t<next = x17> * x1::RefSll_t<next = x4> * ls(x3,x14) & null = null
         |- ls(x8,x17) * ls(x14,x3) * ls(x15,x11) * ls(x6,x3) * ls(x10,x16) * ls(x16,x14) * ls(x18,x8) * ls(x12,x5) * ls(x11,x13).

