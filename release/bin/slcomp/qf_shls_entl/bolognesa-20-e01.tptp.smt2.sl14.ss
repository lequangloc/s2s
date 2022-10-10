
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x6::RefSll_t<next = x12> * ls(x15,x7) * ls(x10,x1) * x14::RefSll_t<next = x7> * x2::RefSll_t<next = x1> * ls(x12,x7) * x9::RefSll_t<next = x19> * x13::RefSll_t<next = x11> * x8::RefSll_t<next = x17> * x16::RefSll_t<next = x1> * x1::RefSll_t<next = x18> * x4::RefSll_t<next = x19> * x17::RefSll_t<next = x11> * x3::RefSll_t<next = x12> * x18::RefSll_t<next = x4> * ls(x20,x12) * x5::RefSll_t<next = x17> * x11::RefSll_t<next = x6> * x19::RefSll_t<next = x1> * ls(x7,x12) & null = null
         |- ls(x15,x7) * ls(x3,x12) * ls(x8,x17) * ls(x14,x7) * ls(x5,x17) * ls(x7,x12) * ls(x10,x1) * ls(x16,x1) * ls(x20,x12) * ls(x13,x11) * ls(x17,x11) * ls(x9,x1) * ls(x11,x7) * ls(x2,x19).

