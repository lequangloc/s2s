
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x2,x7) * x6::RefSll_t<next = x1> * x4::RefSll_t<next = x9> * x3::RefSll_t<next = x2> * x8::RefSll_t<next = x4> * ls(x10,x2) * x5::RefSll_t<next = x7> * x1::RefSll_t<next = x6> * x9::RefSll_t<next = x1> * ls(x7,x2) & null = null
         |- ls(x6,x1) * ls(x10,x2) * ls(x8,x4) * ls(x3,x2) * ls(x5,x7) * ls(x4,x6) * ls(x2,x7) * ls(x7,x2).

