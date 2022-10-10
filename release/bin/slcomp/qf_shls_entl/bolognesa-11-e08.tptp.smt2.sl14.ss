
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x8::RefSll_t<next = x11> * ls(x3,x8) * ls(x6,x4) * x10::RefSll_t<next = x6> * x1::RefSll_t<next = x7> * x2::RefSll_t<next = x7> * x5::RefSll_t<next = x3> * ls(x11,x1) * x9::RefSll_t<next = x7> * x7::RefSll_t<next = x6> * x4::RefSll_t<next = x9> & null = null
         |- ls(x9,x7) * ls(x10,x6) * ls(x2,x7) * ls(x5,x8) * ls(x8,x9).

