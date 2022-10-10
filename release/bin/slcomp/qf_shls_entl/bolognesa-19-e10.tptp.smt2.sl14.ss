
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x6::RefSll_t<next = x18> * x11::RefSll_t<next = x5> * x17::RefSll_t<next = x18> * ls(x2,x10) * ls(x14,x10) * x19::RefSll_t<next = x17> * x1::RefSll_t<next = x13> * x10::RefSll_t<next = x16> * x7::RefSll_t<next = x8> * x16::RefSll_t<next = x1> * x13::RefSll_t<next = x14> * x12::RefSll_t<next = x6> * x4::RefSll_t<next = x9> * x15::RefSll_t<next = x10> * x8::RefSll_t<next = x9> * x9::RefSll_t<next = x17> * x5::RefSll_t<next = x13> * x3::RefSll_t<next = x9> * x18::RefSll_t<next = x17> & null = null
         |- ls(x12,x6) * ls(x2,x10) * ls(x11,x5) * ls(x1,x13) * ls(x15,x10) * ls(x4,x9) * ls(x19,x17) * ls(x7,x8) * ls(x8,x9) * ls(x6,x18) * ls(x3,x18) * ls(x18,x17) * ls(x5,x1).

