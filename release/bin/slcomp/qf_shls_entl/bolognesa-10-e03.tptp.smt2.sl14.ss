
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x5,x7) * x10::RefSll_t<next = x4> * x6::RefSll_t<next = x9> * x7::RefSll_t<next = x3> * x3::RefSll_t<next = x6> * x9::RefSll_t<next = x4> * ls(x2,x4) * ls(x8,x10) * x1::RefSll_t<next = x10> * x4::RefSll_t<next = x10> & null = null
         |- ls(x1,x10) * ls(x5,x7) * ls(x7,x6) * ls(x6,x9) * ls(x9,x4) * ls(x2,x4) * ls(x8,x4) * ls(x4,x10).

