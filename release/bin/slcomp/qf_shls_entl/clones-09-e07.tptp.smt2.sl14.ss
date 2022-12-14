
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x25,x26) * x26::RefSll_t<next = x25> * ls(x22,x23) * x23::RefSll_t<next = x22> * ls(x19,x20) * x20::RefSll_t<next = x19> * ls(x16,x17) * x17::RefSll_t<next = x16> * ls(x13,x14) * x14::RefSll_t<next = x13> * ls(x10,x11) * x11::RefSll_t<next = x10> * ls(x7,x8) * x8::RefSll_t<next = x7> * ls(x4,x5) * x5::RefSll_t<next = x4> * ls(x1,x2) * x2::RefSll_t<next = x1> & null = null & null != x1 & null != x2 & null != x4 & null != x5 & null != x7 & null != x8 & null != x10 & null != x11 & null != x13 & null != x14 & null != x16 & null != x17 & null != x19 & null != x20 & null != x22 & null != x23 & null != x25 & null != x26
         |- ls(x27,x26) * x26::RefSll_t<next = x27> * ls(x24,x23) * x23::RefSll_t<next = x24> * ls(x21,x20) * x20::RefSll_t<next = x21> * ls(x18,x17) * x17::RefSll_t<next = x18> * ls(x15,x14) * x14::RefSll_t<next = x15> * ls(x12,x11) * x11::RefSll_t<next = x12> * ls(x9,x8) * x8::RefSll_t<next = x9> * ls(x6,x5) * x5::RefSll_t<next = x6> * ls(x3,x2) * x2::RefSll_t<next = x3>.

