
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x4::RefSll_t<next = x5> * x3::RefSll_t<next = x9> * ls(x8,x1) * ls(x2,x8) * ls(x1,x2) * x7::RefSll_t<next = x8> * x9::RefSll_t<next = x4> * x5::RefSll_t<next = x1> * x10::RefSll_t<next = x5> * x6::RefSll_t<next = x10> & null = null
         |- ls(x3,x9) * ls(x9,x4) * ls(x6,x10) * ls(x10,x5) * ls(x7,x1) * ls(x4,x8).

