
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x3,x6) * ls(x7,x4) * x1::RefSll_t<next = x10> * x8::RefSll_t<next = x13> * ls(x12,x2) * x6::RefSll_t<next = x9> * ls(x13,x11) * x9::RefSll_t<next = x8> * ls(x5,x7) * ls(x2,x10) * ls(x10,x1) * ls(x11,x4) * ls(x4,x1) & null = null
         |- ls(x3,x8) * ls(x8,x13) * ls(x5,x7) * ls(x13,x4) * ls(x12,x10) * ls(x7,x10) * ls(x10,x1).

