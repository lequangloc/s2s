
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x10::RefSll_t<next = x15> * x4::RefSll_t<next = x12> * x7::RefSll_t<next = x3> * x5::RefSll_t<next = x13> * ls(x6,x3) * x16::RefSll_t<next = x4> * x13::RefSll_t<next = x9> * ls(x11,x12) * x12::RefSll_t<next = x7> * x14::RefSll_t<next = x6> * x9::RefSll_t<next = x8> * x15::RefSll_t<next = x13> * x1::RefSll_t<next = x3> * x2::RefSll_t<next = x8> * ls(x8,x5) * ls(x3,x14) & null = null
         |- ls(x10,x13) * ls(x16,x12) * ls(x11,x7) * ls(x6,x3) * ls(x7,x3) * ls(x1,x6) * ls(x2,x5) * ls(x5,x8).

