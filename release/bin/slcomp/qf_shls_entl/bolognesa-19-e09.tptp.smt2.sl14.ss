
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x14,x18) * x3::RefSll_t<next = x7> * x9::RefSll_t<next = x4> * ls(x6,x1) * ls(x19,x3) * x5::RefSll_t<next = x11> * x4::RefSll_t<next = x13> * x18::RefSll_t<next = x19> * ls(x17,x3) * x1::RefSll_t<next = x18> * ls(x7,x10) * x11::RefSll_t<next = x2> * x15::RefSll_t<next = x3> * x16::RefSll_t<next = x4> * ls(x12,x6) * ls(x10,x3) * x13::RefSll_t<next = x19> * ls(x2,x3) * ls(x8,x14) & null = null
         |- ls(x15,x3) * ls(x17,x3) * ls(x12,x18) * ls(x9,x4) * ls(x16,x4) * ls(x4,x13) * ls(x5,x2) * ls(x8,x18) * ls(x13,x19) * ls(x10,x3) * ls(x18,x3) * ls(x2,x10).

