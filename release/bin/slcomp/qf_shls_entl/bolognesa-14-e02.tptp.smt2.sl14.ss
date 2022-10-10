
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x11::RefSll_t<next = x8> * x5::RefSll_t<next = x13> * x10::RefSll_t<next = x5> * x9::RefSll_t<next = x7> * x7::RefSll_t<next = x3> * x3::RefSll_t<next = x10> * x12::RefSll_t<next = x3> * x13::RefSll_t<next = x9> * x6::RefSll_t<next = x4> * ls(x2,x5) * x14::RefSll_t<next = x12> * x1::RefSll_t<next = x3> * x8::RefSll_t<next = x13> * ls(x4,x12) & null = null
         |- ls(x1,x3) * ls(x2,x5) * ls(x14,x12) * ls(x5,x13) * ls(x6,x3) * ls(x11,x8) * ls(x8,x5).

