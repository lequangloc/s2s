
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x11::RefSll_t<next = x13> * ls(x10,x6) * x2::RefSll_t<next = x11> * x3::RefSll_t<next = x1> * ls(x4,x7) * x14::RefSll_t<next = x11> * x7::RefSll_t<next = x5> * ls(x6,x8) * ls(x8,x1) * x15::RefSll_t<next = x4> * x13::RefSll_t<next = x16> * x1::RefSll_t<next = x14> * x9::RefSll_t<next = x4> * ls(x17,x2) * x16::RefSll_t<next = x9> * x5::RefSll_t<next = x6> * x12::RefSll_t<next = x1> & null = null
         |- ls(x3,x1) * ls(x17,x11) * ls(x12,x14) * ls(x15,x4) * ls(x10,x6) * ls(x14,x1).

