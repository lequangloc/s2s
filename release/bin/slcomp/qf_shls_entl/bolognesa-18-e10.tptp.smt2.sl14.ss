
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x18::RefSll_t<next = x4> * ls(x11,x18) * x14::RefSll_t<next = x5> * x6::RefSll_t<next = x18> * x8::RefSll_t<next = x1> * x15::RefSll_t<next = x9> * x16::RefSll_t<next = x2> * x2::RefSll_t<next = x15> * x5::RefSll_t<next = x17> * ls(x10,x17) * x4::RefSll_t<next = x17> * x1::RefSll_t<next = x10> * x9::RefSll_t<next = x6> * x12::RefSll_t<next = x3> * x17::RefSll_t<next = x18> * x3::RefSll_t<next = x12> * ls(x13,x15) * ls(x7,x14) & null = null
         |- ls(x13,x15) * ls(x12,x3) * ls(x11,x18) * ls(x7,x14) * ls(x3,x12) * ls(x16,x2) * ls(x8,x1) * ls(x14,x17) * ls(x1,x18) * ls(x2,x18) * ls(x18,x17).

