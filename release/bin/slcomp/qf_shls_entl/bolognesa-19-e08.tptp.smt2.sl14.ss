
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x14::RefSll_t<next = x17> * x6::RefSll_t<next = x11> * x8::RefSll_t<next = x18> * ls(x2,x15) * ls(x4,x3) * x12::RefSll_t<next = x5> * x10::RefSll_t<next = x16> * ls(x1,x17) * ls(x5,x6) * ls(x19,x13) * ls(x16,x15) * ls(x3,x17) * ls(x7,x14) * x15::RefSll_t<next = x12> * ls(x13,x3) * ls(x9,x10) * x11::RefSll_t<next = x4> * x17::RefSll_t<next = x8> * x18::RefSll_t<next = x6> & null = null
         |- ls(x1,x17) * ls(x19,x3) * ls(x18,x6) * ls(x9,x10) * ls(x10,x16) * ls(x2,x15) * ls(x16,x12) * ls(x7,x17) * ls(x12,x18).

