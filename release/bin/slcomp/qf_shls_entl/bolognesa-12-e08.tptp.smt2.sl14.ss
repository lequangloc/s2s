
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x8,x7) * x3::RefSll_t<next = x12> * x6::RefSll_t<next = x9> * ls(x2,x11) * ls(x4,x6) * ls(x9,x12) * x12::RefSll_t<next = x6> * x5::RefSll_t<next = x4> * x10::RefSll_t<next = x8> * x7::RefSll_t<next = x11> * x1::RefSll_t<next = x6> * x11::RefSll_t<next = x6> & null = null
         |- ls(x1,x6) * ls(x10,x8) * ls(x8,x7) * ls(x7,x11) * ls(x3,x6) * ls(x2,x6) * ls(x5,x12).

