
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x19::RefSll_t<next = x13> * ls(x1,x18) * x11::RefSll_t<next = x18> * x18::RefSll_t<next = x16> * ls(x16,x19) * x2::RefSll_t<next = x19> * ls(x4,x12) * x6::RefSll_t<next = x7> * ls(x10,x2) * x5::RefSll_t<next = x8> * x14::RefSll_t<next = x6> * x3::RefSll_t<next = x10> * x7::RefSll_t<next = x18> * x12::RefSll_t<next = x15> * x9::RefSll_t<next = x16> * x17::RefSll_t<next = x5> * x13::RefSll_t<next = x9> * x15::RefSll_t<next = x17> * x8::RefSll_t<next = x7> & null = null
         |- ls(x4,x12) * ls(x14,x6) * ls(x12,x15) * ls(x11,x18) * ls(x15,x7) * ls(x6,x18) * ls(x1,x16) * ls(x16,x19) * ls(x3,x16).

