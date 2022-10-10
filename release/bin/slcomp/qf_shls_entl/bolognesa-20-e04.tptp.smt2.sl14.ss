
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x15::RefSll_t<next = x6> * ls(x5,x4) * x16::RefSll_t<next = x9> * x2::RefSll_t<next = x20> * x11::RefSll_t<next = x3> * x12::RefSll_t<next = x19> * x17::RefSll_t<next = x14> * x14::RefSll_t<next = x15> * x19::RefSll_t<next = x10> * x13::RefSll_t<next = x1> * ls(x8,x13) * x10::RefSll_t<next = x9> * x1::RefSll_t<next = x3> * ls(x9,x15) * x6::RefSll_t<next = x5> * ls(x7,x3) * x18::RefSll_t<next = x12> * ls(x20,x7) * x4::RefSll_t<next = x1> * ls(x3,x16) & null = null
         |- ls(x8,x13) * ls(x18,x19) * ls(x2,x20) * ls(x11,x3) * ls(x20,x7) * ls(x19,x9) * ls(x7,x3) * ls(x13,x1) * ls(x9,x15) * ls(x17,x9).

