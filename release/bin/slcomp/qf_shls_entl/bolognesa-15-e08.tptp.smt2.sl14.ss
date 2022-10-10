
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x13,x11) * ls(x8,x10) * x4::RefSll_t<next = x9> * ls(x6,x13) * x10::RefSll_t<next = x4> * x2::RefSll_t<next = x6> * x14::RefSll_t<next = x11> * x11::RefSll_t<next = x9> * x12::RefSll_t<next = x3> * ls(x9,x12) * ls(x5,x3) * x15::RefSll_t<next = x2> * ls(x7,x8) * ls(x1,x4) * ls(x3,x5) & null = null
         |- ls(x14,x11) * ls(x15,x6) * ls(x1,x4) * ls(x6,x9) * ls(x7,x5) * ls(x5,x3).

