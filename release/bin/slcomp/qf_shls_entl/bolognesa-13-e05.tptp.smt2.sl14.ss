
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x9::RefSll_t<next = x2> * x7::RefSll_t<next = x10> * ls(x12,x5) * x4::RefSll_t<next = x13> * x10::RefSll_t<next = x13> * x3::RefSll_t<next = x9> * ls(x13,x7) * x11::RefSll_t<next = x13> * ls(x1,x12) * x6::RefSll_t<next = x5> * x5::RefSll_t<next = x9> * x8::RefSll_t<next = x4> * x2::RefSll_t<next = x1> & null = null
         |- ls(x8,x4) * ls(x7,x10) * ls(x4,x13) * ls(x12,x5) * ls(x11,x13) * ls(x3,x9) * ls(x6,x12) * ls(x10,x7).

