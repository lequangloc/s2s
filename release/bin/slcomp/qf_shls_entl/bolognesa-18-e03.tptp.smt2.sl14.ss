
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x15,x7) * x18::RefSll_t<next = x7> * ls(x3,x5) * x14::RefSll_t<next = x8> * ls(x4,x1) * ls(x6,x13) * x17::RefSll_t<next = x6> * x13::RefSll_t<next = x5> * ls(x1,x7) * x5::RefSll_t<next = x3> * ls(x2,x11) * x7::RefSll_t<next = x13> * x8::RefSll_t<next = x3> * x16::RefSll_t<next = x7> * x11::RefSll_t<next = x10> * ls(x12,x18) * x10::RefSll_t<next = x1> * x9::RefSll_t<next = x10> & null = null
         |- ls(x16,x7) * ls(x12,x18) * ls(x9,x10) * ls(x17,x6) * ls(x14,x8) * ls(x8,x5) * ls(x2,x1) * ls(x18,x7) * ls(x6,x13) * ls(x15,x7) * ls(x4,x3).

