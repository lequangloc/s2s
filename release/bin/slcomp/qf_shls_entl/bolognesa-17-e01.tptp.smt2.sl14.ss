
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x7::RefSll_t<next = x2> * x6::RefSll_t<next = x11> * x12::RefSll_t<next = x4> * ls(x9,x10) * x10::RefSll_t<next = x13> * x8::RefSll_t<next = x7> * x11::RefSll_t<next = x13> * x5::RefSll_t<next = x9> * x16::RefSll_t<next = x14> * x1::RefSll_t<next = x10> * x14::RefSll_t<next = x6> * x17::RefSll_t<next = x7> * ls(x2,x3) * x13::RefSll_t<next = x5> * x3::RefSll_t<next = x7> * x4::RefSll_t<next = x12> * ls(x15,x2) & null = null
         |- ls(x16,x14) * ls(x1,x10) * ls(x15,x2) * ls(x3,x7) * ls(x10,x13) * ls(x12,x4) * ls(x17,x7) * ls(x14,x6) * ls(x4,x12) * ls(x6,x13) * ls(x8,x3) * ls(x13,x10).

