
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x4::RefSll_t<next = x3> * x7::RefSll_t<next = x1> * ls(x9,x2) * ls(x3,x11) * ls(x12,x8) * x6::RefSll_t<next = x1> * x5::RefSll_t<next = x10> * ls(x2,x1) * x8::RefSll_t<next = x5> * x10::RefSll_t<next = x3> * x11::RefSll_t<next = x12> * x1::RefSll_t<next = x12> & null = null
         |- ls(x4,x3) * ls(x6,x1) * ls(x11,x12) * ls(x9,x2) * ls(x2,x1) * ls(x7,x1) * ls(x1,x11).

