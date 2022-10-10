
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x16::RefSll_t<next = x9> * ls(x2,x1) * x17::RefSll_t<next = x8> * x1::RefSll_t<next = x4> * x5::RefSll_t<next = x13> * ls(x10,x17) * x12::RefSll_t<next = x15> * x3::RefSll_t<next = x12> * ls(x8,x13) * ls(x4,x1) * x15::RefSll_t<next = x12> * x7::RefSll_t<next = x16> * x11::RefSll_t<next = x10> * ls(x14,x5) * x6::RefSll_t<next = x2> * x9::RefSll_t<next = x1> * ls(x18,x7) * x13::RefSll_t<next = x9> & null = null
         |- ls(x11,x10) * ls(x15,x12) * ls(x10,x13) * ls(x3,x12) * ls(x18,x9) * ls(x12,x15) * ls(x14,x5) * ls(x6,x1) * ls(x5,x4) * ls(x4,x1).

