
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x3::RefSll_t<next = x9> * x4::RefSll_t<next = x3> * x1::RefSll_t<next = x3> * x8::RefSll_t<next = x10> * x5::RefSll_t<next = x1> * x6::RefSll_t<next = x9> * ls(x10,x5) * x2::RefSll_t<next = x4> * x11::RefSll_t<next = x9> * x7::RefSll_t<next = x9> * x9::RefSll_t<next = x3> & null = null
         |- ls(x11,x9) * ls(x2,x4) * ls(x7,x9) * ls(x4,x3) * ls(x8,x10) * ls(x10,x5) * ls(x6,x3) * ls(x5,x3) * ls(x3,x9).

