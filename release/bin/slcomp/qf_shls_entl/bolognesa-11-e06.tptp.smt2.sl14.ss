
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x2::RefSll_t<next = x9> * ls(x4,x7) * x11::RefSll_t<next = x8> * ls(x9,x1) * x7::RefSll_t<next = x11> * ls(x10,x7) * x6::RefSll_t<next = x9> * ls(x8,x11) * x3::RefSll_t<next = x9> * x1::RefSll_t<next = x5> * x5::RefSll_t<next = x2> & null = null
         |- ls(x10,x7) * ls(x4,x7) * ls(x7,x11) * ls(x8,x11) * ls(x11,x8) * ls(x3,x9) * ls(x2,x9) * ls(x6,x2).

