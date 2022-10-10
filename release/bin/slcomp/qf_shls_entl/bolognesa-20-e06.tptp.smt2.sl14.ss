
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x16::RefSll_t<next = x2> * x2::RefSll_t<next = x16> * ls(x7,x18) * ls(x19,x13) * x18::RefSll_t<next = x14> * x17::RefSll_t<next = x10> * ls(x8,x1) * x4::RefSll_t<next = x16> * x1::RefSll_t<next = x20> * x20::RefSll_t<next = x17> * ls(x13,x4) * x14::RefSll_t<next = x20> * x11::RefSll_t<next = x18> * x15::RefSll_t<next = x6> * x9::RefSll_t<next = x2> * x10::RefSll_t<next = x6> * x3::RefSll_t<next = x2> * x12::RefSll_t<next = x20> * x5::RefSll_t<next = x3> * x6::RefSll_t<next = x4> & null = null
         |- ls(x7,x18) * ls(x15,x6) * ls(x11,x18) * ls(x9,x2) * ls(x8,x1) * ls(x1,x20) * ls(x12,x20) * ls(x19,x13) * ls(x18,x4) * ls(x13,x4) * ls(x5,x16) * ls(x4,x2).

