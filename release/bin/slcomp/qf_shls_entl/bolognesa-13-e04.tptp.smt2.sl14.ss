
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x7::RefSll_t<next = x11> * ls(x5,x11) * ls(x1,x4) * ls(x3,x11) * x2::RefSll_t<next = x5> * x10::RefSll_t<next = x13> * x8::RefSll_t<next = x11> * x9::RefSll_t<next = x8> * x6::RefSll_t<next = x12> * ls(x12,x4) * x11::RefSll_t<next = x4> * x4::RefSll_t<next = x3> * x13::RefSll_t<next = x12> & null = null
         |- ls(x1,x4) * ls(x3,x11) * ls(x6,x12) * ls(x7,x11) * ls(x2,x11) * ls(x10,x12) * ls(x12,x4) * ls(x9,x3).

