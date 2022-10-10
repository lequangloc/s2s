
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x7::RefSll_t<next = x10> * x4::RefSll_t<next = x11> * x6::RefSll_t<next = x5> * ls(x9,x5) * x10::RefSll_t<next = x12> * ls(x3,x8) * x1::RefSll_t<next = x2> * x11::RefSll_t<next = x1> * x5::RefSll_t<next = x4> * x12::RefSll_t<next = x9> * ls(x2,x8) * ls(x8,x11) & null = null
         |- ls(x7,x12) * ls(x12,x5) * ls(x3,x8) * ls(x8,x11) * ls(x6,x11) * ls(x11,x8).

