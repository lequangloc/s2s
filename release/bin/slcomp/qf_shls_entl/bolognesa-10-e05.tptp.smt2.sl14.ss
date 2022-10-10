
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x3,x6) * x9::RefSll_t<next = x1> * x7::RefSll_t<next = x9> * x6::RefSll_t<next = x7> * ls(x8,x9) * ls(x1,x9) * x2::RefSll_t<next = x3> * x5::RefSll_t<next = x1> * x4::RefSll_t<next = x9> * ls(x10,x5) & null = null
         |- ls(x10,x5) * ls(x5,x1) * ls(x2,x9) * ls(x4,x9) * ls(x8,x1) * ls(x1,x9).

