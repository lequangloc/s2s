
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x3,x1) * ls(x13,x14) * x15::RefSll_t<next = x3> * x6::RefSll_t<next = x13> * x8::RefSll_t<next = x15> * ls(x9,x13) * x7::RefSll_t<next = x11> * x2::RefSll_t<next = x7> * x10::RefSll_t<next = x14> * ls(x11,x3) * x12::RefSll_t<next = x9> * ls(x4,x6) * x1::RefSll_t<next = x12> * x14::RefSll_t<next = x11> * ls(x5,x11) & null = null
         |- ls(x10,x14) * ls(x9,x13) * ls(x2,x7) * ls(x7,x11) * ls(x8,x15) * ls(x15,x3) * ls(x5,x11) * ls(x4,x9).

