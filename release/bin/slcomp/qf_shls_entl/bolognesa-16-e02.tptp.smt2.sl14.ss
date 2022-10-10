
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x3::RefSll_t<next = x4> * x8::RefSll_t<next = x14> * x2::RefSll_t<next = x11> * ls(x5,x15) * x14::RefSll_t<next = x1> * x12::RefSll_t<next = x11> * x13::RefSll_t<next = x1> * x9::RefSll_t<next = x11> * x16::RefSll_t<next = x14> * x1::RefSll_t<next = x2> * ls(x4,x15) * x7::RefSll_t<next = x11> * x10::RefSll_t<next = x6> * ls(x6,x5) * x11::RefSll_t<next = x1> * x15::RefSll_t<next = x6> & null = null
         |- ls(x13,x1) * ls(x12,x11) * ls(x8,x14) * ls(x16,x14) * ls(x3,x15) * ls(x2,x11) * ls(x9,x11) * ls(x14,x1) * ls(x15,x6) * ls(x10,x15) * ls(x7,x2).

