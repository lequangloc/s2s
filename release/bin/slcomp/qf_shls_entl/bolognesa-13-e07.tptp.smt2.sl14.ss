
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x1::RefSll_t<next = x4> * x10::RefSll_t<next = x7> * x6::RefSll_t<next = x8> * ls(x5,x1) * x13::RefSll_t<next = x6> * x7::RefSll_t<next = x12> * x12::RefSll_t<next = x10> * ls(x11,x9) * x9::RefSll_t<next = x1> * x4::RefSll_t<next = x9> * ls(x8,x10) * ls(x3,x9) * ls(x2,x13) & null = null
         |- ls(x3,x9) * ls(x11,x9) * ls(x12,x10) * ls(x2,x6) * ls(x6,x8) * ls(x4,x9) * ls(x8,x10) * ls(x5,x1) * ls(x10,x12) * ls(x9,x4).

