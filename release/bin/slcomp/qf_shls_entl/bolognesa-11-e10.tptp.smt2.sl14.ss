
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x1,x3) * x8::RefSll_t<next = x11> * x5::RefSll_t<next = x8> * x11::RefSll_t<next = x10> * ls(x3,x1) * ls(x10,x9) * x4::RefSll_t<next = x6> * x6::RefSll_t<next = x4> * x9::RefSll_t<next = x10> * x7::RefSll_t<next = x1> * ls(x2,x6) & null = null
         |- ls(x2,x4) * ls(x9,x10) * ls(x7,x3) * ls(x4,x6) * ls(x3,x1) * ls(x5,x11) * ls(x11,x9).

