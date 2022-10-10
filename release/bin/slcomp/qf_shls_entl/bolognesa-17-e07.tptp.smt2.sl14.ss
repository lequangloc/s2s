
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x7::RefSll_t<next = x6> * x6::RefSll_t<next = x4> * ls(x8,x14) * x2::RefSll_t<next = x14> * x17::RefSll_t<next = x4> * ls(x9,x5) * x16::RefSll_t<next = x6> * x11::RefSll_t<next = x15> * x5::RefSll_t<next = x15> * x10::RefSll_t<next = x8> * x4::RefSll_t<next = x15> * ls(x14,x17) * ls(x1,x2) * x3::RefSll_t<next = x16> * x15::RefSll_t<next = x13> * x12::RefSll_t<next = x4> * x13::RefSll_t<next = x9> & null = null
         |- ls(x10,x8) * ls(x5,x15) * ls(x7,x6) * ls(x11,x15) * ls(x12,x4) * ls(x1,x14) * ls(x8,x4) * ls(x3,x5).

