
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x14,x13) * x17::RefSll_t<next = x14> * x16::RefSll_t<next = x10> * x20::RefSll_t<next = x16> * x3::RefSll_t<next = x18> * ls(x8,x17) * x6::RefSll_t<next = x2> * x9::RefSll_t<next = x18> * ls(x15,x8) * ls(x2,x15) * x4::RefSll_t<next = x17> * x19::RefSll_t<next = x1> * ls(x18,x5) * ls(x1,x4) * x10::RefSll_t<next = x2> * x13::RefSll_t<next = x10> * x5::RefSll_t<next = x20> * ls(x12,x16) * x11::RefSll_t<next = x9> * x7::RefSll_t<next = x8> & null = null
         |- ls(x11,x9) * ls(x7,x8) * ls(x8,x17) * ls(x9,x18) * ls(x3,x16) * ls(x12,x10) * ls(x6,x2) * ls(x19,x8).

