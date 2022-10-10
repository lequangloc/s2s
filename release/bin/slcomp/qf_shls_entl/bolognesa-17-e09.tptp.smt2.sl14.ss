
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x13,x5) * x17::RefSll_t<next = x8> * x9::RefSll_t<next = x5> * ls(x15,x3) * ls(x1,x2) * x14::RefSll_t<next = x2> * x12::RefSll_t<next = x10> * x7::RefSll_t<next = x10> * x8::RefSll_t<next = x9> * x2::RefSll_t<next = x3> * x10::RefSll_t<next = x9> * x3::RefSll_t<next = x17> * x4::RefSll_t<next = x15> * x6::RefSll_t<next = x12> * x5::RefSll_t<next = x3> * x16::RefSll_t<next = x10> * x11::RefSll_t<next = x9> & null = null
         |- ls(x13,x5) * ls(x6,x12) * ls(x12,x10) * ls(x8,x9) * ls(x4,x15) * ls(x16,x10) * ls(x11,x9) * ls(x1,x2) * ls(x15,x3) * ls(x14,x3) * ls(x7,x8).

