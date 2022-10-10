
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x5::RefSll_t<next = x7> * x17::RefSll_t<next = x3> * x13::RefSll_t<next = x10> * x15::RefSll_t<next = x2> * ls(x12,x8) * x7::RefSll_t<next = x4> * x6::RefSll_t<next = x3> * x16::RefSll_t<next = x1> * x8::RefSll_t<next = x6> * x1::RefSll_t<next = x4> * ls(x11,x5) * x2::RefSll_t<next = x12> * ls(x14,x17) * x10::RefSll_t<next = x18> * x4::RefSll_t<next = x11> * x3::RefSll_t<next = x7> * ls(x9,x6) * x18::RefSll_t<next = x5> & null = null
         |- ls(x13,x10) * ls(x11,x5) * ls(x14,x17) * ls(x17,x3) * ls(x10,x18) * ls(x16,x1) * ls(x15,x6) * ls(x1,x4) * ls(x9,x7) * ls(x18,x11).

