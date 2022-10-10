
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x14,x17) * x17::RefSll_t<next = x13> * x1::RefSll_t<next = x7> * x4::RefSll_t<next = x6> * x10::RefSll_t<next = x8> * x8::RefSll_t<next = x2> * ls(x3,x17) * x2::RefSll_t<next = x5> * x6::RefSll_t<next = x13> * x16::RefSll_t<next = x7> * x9::RefSll_t<next = x12> * x18::RefSll_t<next = x10> * ls(x7,x14) * ls(x12,x14) * x5::RefSll_t<next = x1> * x13::RefSll_t<next = x18> * x15::RefSll_t<next = x11> * ls(x11,x8) & null = null
         |- ls(x9,x12) * ls(x18,x10) * ls(x15,x8) * ls(x16,x7) * ls(x4,x6) * ls(x12,x14) * ls(x3,x17) * ls(x6,x13) * ls(x10,x18).

