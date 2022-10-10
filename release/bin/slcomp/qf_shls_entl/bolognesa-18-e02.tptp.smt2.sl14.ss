
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x8,x6) * x6::RefSll_t<next = x11> * ls(x15,x1) * x5::RefSll_t<next = x6> * x2::RefSll_t<next = x7> * ls(x11,x4) * ls(x9,x5) * x13::RefSll_t<next = x14> * ls(x16,x18) * x7::RefSll_t<next = x14> * x3::RefSll_t<next = x18> * x4::RefSll_t<next = x13> * ls(x18,x15) * x12::RefSll_t<next = x16> * x10::RefSll_t<next = x4> * x14::RefSll_t<next = x10> * x17::RefSll_t<next = x4> * x1::RefSll_t<next = x16> & null = null
         |- ls(x8,x6) * ls(x10,x4) * ls(x9,x4) * ls(x15,x1) * ls(x3,x18) * ls(x2,x14) * ls(x12,x16) * ls(x17,x10) * ls(x1,x15).

