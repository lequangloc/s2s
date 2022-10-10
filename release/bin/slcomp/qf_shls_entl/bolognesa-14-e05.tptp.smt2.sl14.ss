
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x11::RefSll_t<next = x6> * ls(x4,x10) * x13::RefSll_t<next = x9> * ls(x14,x12) * x5::RefSll_t<next = x9> * ls(x10,x11) * x7::RefSll_t<next = x12> * ls(x2,x12) * ls(x3,x12) * x9::RefSll_t<next = x4> * x1::RefSll_t<next = x6> * x12::RefSll_t<next = x7> * ls(x6,x4) * x8::RefSll_t<next = x4> & null = null
         |- ls(x7,x12) * ls(x3,x12) * ls(x5,x9) * ls(x8,x4) * ls(x13,x10) * ls(x1,x6) * ls(x2,x12) * ls(x14,x7) * ls(x10,x4).

