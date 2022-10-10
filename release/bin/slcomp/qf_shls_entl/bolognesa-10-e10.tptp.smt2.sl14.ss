
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x1::RefSll_t<next = x2> * x4::RefSll_t<next = x6> * x9::RefSll_t<next = x3> * ls(x7,x2) * ls(x5,x4) * x3::RefSll_t<next = x2> * x8::RefSll_t<next = x9> * x6::RefSll_t<next = x9> * x2::RefSll_t<next = x10> * ls(x10,x1) & null = null
         |- ls(x5,x4) * ls(x7,x2) * ls(x1,x2) * ls(x4,x6) * ls(x8,x9) * ls(x6,x3) * ls(x3,x2) * ls(x2,x1).

