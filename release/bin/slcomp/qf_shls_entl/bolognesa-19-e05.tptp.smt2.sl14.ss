
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x14::RefSll_t<next = x12> * x17::RefSll_t<next = x6> * ls(x1,x7) * ls(x16,x4) * x3::RefSll_t<next = x12> * x15::RefSll_t<next = x2> * x10::RefSll_t<next = x18> * x5::RefSll_t<next = x15> * x18::RefSll_t<next = x8> * x12::RefSll_t<next = x19> * x13::RefSll_t<next = x1> * ls(x6,x3) * x2::RefSll_t<next = x10> * x11::RefSll_t<next = x5> * ls(x19,x1) * x4::RefSll_t<next = x12> * x8::RefSll_t<next = x7> * ls(x7,x2) * x9::RefSll_t<next = x11> & null = null
         |- ls(x16,x4) * ls(x4,x12) * ls(x8,x7) * ls(x9,x11) * ls(x17,x3) * ls(x14,x12) * ls(x11,x2) * ls(x13,x1) * ls(x3,x8).

