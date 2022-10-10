
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x14::RefSll_t<next = x1> * ls(x3,x15) * x7::RefSll_t<next = x2> * x12::RefSll_t<next = x1> * x13::RefSll_t<next = x14> * ls(x1,x5) * ls(x9,x4) * ls(x4,x7) * x15::RefSll_t<next = x8> * x5::RefSll_t<next = x4> * x11::RefSll_t<next = x2> * ls(x2,x8) * x6::RefSll_t<next = x15> * x10::RefSll_t<next = x3> * x8::RefSll_t<next = x11> & null = null
         |- ls(x6,x15) * ls(x10,x3) * ls(x9,x4) * ls(x12,x1) * ls(x3,x8) * ls(x11,x2) * ls(x13,x11).

