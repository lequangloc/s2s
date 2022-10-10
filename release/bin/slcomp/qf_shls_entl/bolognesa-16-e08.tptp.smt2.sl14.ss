
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x14,x9) * ls(x9,x10) * ls(x3,x2) * x1::RefSll_t<next = x4> * x13::RefSll_t<next = x15> * x8::RefSll_t<next = x9> * x2::RefSll_t<next = x1> * x11::RefSll_t<next = x2> * x10::RefSll_t<next = x11> * ls(x12,x3) * x7::RefSll_t<next = x1> * ls(x4,x9) * x15::RefSll_t<next = x7> * ls(x6,x15) * x16::RefSll_t<next = x1> * x5::RefSll_t<next = x3> & null = null
         |- ls(x14,x9) * ls(x16,x1) * ls(x6,x15) * ls(x5,x3) * ls(x13,x15) * ls(x12,x1) * ls(x8,x9) * ls(x15,x2).

