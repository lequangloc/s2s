
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x2::RefSll_t<next = x10> * ls(x9,x8) * x17::RefSll_t<next = x7> * x18::RefSll_t<next = x12> * ls(x8,x5) * ls(x10,x11) * ls(x4,x17) * x7::RefSll_t<next = x17> * ls(x5,x13) * x19::RefSll_t<next = x17> * x12::RefSll_t<next = x11> * ls(x14,x17) * x6::RefSll_t<next = x1> * x3::RefSll_t<next = x7> * x13::RefSll_t<next = x6> * x15::RefSll_t<next = x13> * x11::RefSll_t<next = x13> * ls(x1,x8) * x16::RefSll_t<next = x18> & null = null
         |- ls(x15,x13) * ls(x1,x8) * ls(x19,x17) * ls(x3,x7) * ls(x2,x11) * ls(x16,x13) * ls(x4,x17) * ls(x9,x1) * ls(x14,x7) * ls(x7,x17).

