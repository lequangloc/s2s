
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x8,x12) * x3::RefSll_t<next = x10> * ls(x13,x5) * x14::RefSll_t<next = x5> * ls(x5,x15) * ls(x7,x16) * x11::RefSll_t<next = x1> * x9::RefSll_t<next = x16> * x12::RefSll_t<next = x9> * ls(x16,x3) * x15::RefSll_t<next = x16> * x2::RefSll_t<next = x10> * ls(x4,x6) * x10::RefSll_t<next = x9> * x6::RefSll_t<next = x9> * x1::RefSll_t<next = x8> & null = null
         |- ls(x2,x10) * ls(x13,x5) * ls(x4,x9) * ls(x14,x5) * ls(x7,x16) * ls(x11,x16) * ls(x5,x9).

