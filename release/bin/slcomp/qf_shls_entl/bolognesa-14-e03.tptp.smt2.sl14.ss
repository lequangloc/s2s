
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x14::RefSll_t<next = x4> * x9::RefSll_t<next = x12> * ls(x13,x7) * x5::RefSll_t<next = x4> * x2::RefSll_t<next = x5> * x1::RefSll_t<next = x4> * ls(x4,x7) * x10::RefSll_t<next = x9> * ls(x11,x10) * x12::RefSll_t<next = x13> * x6::RefSll_t<next = x4> * ls(x8,x4) * x3::RefSll_t<next = x6> * ls(x7,x3) & null = null
         |- ls(x14,x4) * ls(x3,x6) * ls(x11,x9) * ls(x8,x4) * ls(x1,x4) * ls(x9,x7) * ls(x2,x4) * ls(x6,x3).

