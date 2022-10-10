
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x6,x15) * ls(x4,x2) * x19::RefSll_t<next = x13> * x8::RefSll_t<next = x9> * x5::RefSll_t<next = x2> * x15::RefSll_t<next = x13> * x3::RefSll_t<next = x4> * x11::RefSll_t<next = x15> * x16::RefSll_t<next = x5> * x18::RefSll_t<next = x4> * x9::RefSll_t<next = x1> * x2::RefSll_t<next = x8> * x17::RefSll_t<next = x2> * ls(x1,x3) * ls(x14,x7) * x10::RefSll_t<next = x1> * x7::RefSll_t<next = x18> * x12::RefSll_t<next = x13> * ls(x13,x9) & null = null
         |- ls(x10,x1) * ls(x11,x15) * ls(x14,x18) * ls(x18,x4) * ls(x4,x2) * ls(x6,x13) * ls(x19,x13) * ls(x17,x2) * ls(x12,x9) * ls(x16,x4).

