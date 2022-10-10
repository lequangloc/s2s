
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x7::RefSll_t<next = x2> * x2::RefSll_t<next = x9> * x14::RefSll_t<next = x12> * x4::RefSll_t<next = x8> * x3::RefSll_t<next = x10> * x13::RefSll_t<next = x12> * x12::RefSll_t<next = x4> * x6::RefSll_t<next = x10> * x11::RefSll_t<next = x13> * x10::RefSll_t<next = x11> * x1::RefSll_t<next = x2> * x9::RefSll_t<next = x7> * x5::RefSll_t<next = x9> * ls(x8,x10) & null = null
         |- ls(x14,x12) * ls(x5,x9) * ls(x1,x2) * ls(x6,x10) * ls(x3,x10) * ls(x13,x12) * ls(x9,x7) * ls(x7,x9) * ls(x12,x13).

