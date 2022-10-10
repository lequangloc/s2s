
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x16::RefSll_t<next = x7> * x8::RefSll_t<next = x9> * x11::RefSll_t<next = x13> * ls(x14,x17) * ls(x4,x11) * x2::RefSll_t<next = x4> * ls(x3,x13) * x10::RefSll_t<next = x11> * x13::RefSll_t<next = x9> * x17::RefSll_t<next = x15> * x5::RefSll_t<next = x12> * ls(x7,x13) * x9::RefSll_t<next = x14> * x15::RefSll_t<next = x13> * x1::RefSll_t<next = x6> * x6::RefSll_t<next = x16> * x12::RefSll_t<next = x14> & null = null
         |- ls(x8,x9) * ls(x9,x14) * ls(x2,x4) * ls(x1,x6) * ls(x4,x11) * ls(x3,x13) * ls(x6,x7) * ls(x5,x12) * ls(x10,x13) * ls(x7,x13) * ls(x12,x9).

