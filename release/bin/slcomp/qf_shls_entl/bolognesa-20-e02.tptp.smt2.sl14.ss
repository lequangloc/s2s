
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x14::RefSll_t<next = x13> * x18::RefSll_t<next = x1> * x15::RefSll_t<next = x3> * x20::RefSll_t<next = x9> * x6::RefSll_t<next = x5> * x8::RefSll_t<next = x15> * ls(x4,x3) * x10::RefSll_t<next = x8> * x1::RefSll_t<next = x19> * ls(x2,x9) * x12::RefSll_t<next = x7> * x17::RefSll_t<next = x4> * x16::RefSll_t<next = x17> * x9::RefSll_t<next = x11> * ls(x5,x16) * x13::RefSll_t<next = x18> * ls(x11,x7) * x7::RefSll_t<next = x18> * ls(x19,x14) * x3::RefSll_t<next = x17> & null = null
         |- ls(x13,x18) * ls(x20,x9) * ls(x10,x8) * ls(x2,x7) * ls(x6,x17) * ls(x4,x3) * ls(x12,x13) * ls(x8,x4).

