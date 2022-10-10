
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x4::RefSll_t<next = x12> * ls(x9,x10) * x3::RefSll_t<next = x11> * x7::RefSll_t<next = x9> * x5::RefSll_t<next = x2> * ls(x12,x4) * x10::RefSll_t<next = x9> * x1::RefSll_t<next = x2> * x11::RefSll_t<next = x7> * ls(x2,x11) * x6::RefSll_t<next = x10> * x8::RefSll_t<next = x4> & null = null
         |- ls(x6,x10) * ls(x12,x4) * ls(x8,x12) * ls(x5,x2) * ls(x1,x11) * ls(x3,x7) * ls(x10,x9) * ls(x7,x10).

