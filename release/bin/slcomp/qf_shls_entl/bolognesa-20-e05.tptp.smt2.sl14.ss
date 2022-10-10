
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x18,x11) * ls(x2,x6) * x1::RefSll_t<next = x10> * x14::RefSll_t<next = x4> * x15::RefSll_t<next = x6> * x16::RefSll_t<next = x7> * x11::RefSll_t<next = x7> * x9::RefSll_t<next = x6> * ls(x7,x4) * x4::RefSll_t<next = x7> * ls(x13,x1) * ls(x20,x12) * x3::RefSll_t<next = x10> * ls(x6,x3) * ls(x19,x18) * x10::RefSll_t<next = x6> * ls(x8,x14) * x12::RefSll_t<next = x5> * x17::RefSll_t<next = x20> * x5::RefSll_t<next = x11> & null = null
         |- ls(x2,x6) * ls(x16,x7) * ls(x17,x20) * ls(x20,x12) * ls(x15,x6) * ls(x9,x3) * ls(x8,x4) * ls(x12,x11) * ls(x4,x7) * ls(x19,x11) * ls(x13,x10) * ls(x3,x6) * ls(x11,x4).

