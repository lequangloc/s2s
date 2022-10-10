
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x2,x12) * ls(x10,x5) * x14::RefSll_t<next = x3> * x1::RefSll_t<next = x11> * x9::RefSll_t<next = x7> * x16::RefSll_t<next = x10> * x8::RefSll_t<next = x9> * x13::RefSll_t<next = x2> * x4::RefSll_t<next = x3> * x11::RefSll_t<next = x8> * x6::RefSll_t<next = x16> * ls(x12,x16) * x5::RefSll_t<next = x1> * x3::RefSll_t<next = x10> * x7::RefSll_t<next = x1> * ls(x15,x12) & null = null
         |- ls(x9,x7) * ls(x6,x16) * ls(x14,x3) * ls(x4,x3) * ls(x13,x12) * ls(x15,x12) * ls(x12,x16) * ls(x3,x10) * ls(x16,x1) * ls(x7,x9).

