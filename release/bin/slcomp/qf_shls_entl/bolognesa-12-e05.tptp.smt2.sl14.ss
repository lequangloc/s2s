
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x5::RefSll_t<next = x11> * x1::RefSll_t<next = x9> * x3::RefSll_t<next = x4> * x9::RefSll_t<next = x7> * x4::RefSll_t<next = x9> * x7::RefSll_t<next = x10> * x8::RefSll_t<next = x10> * x6::RefSll_t<next = x7> * x12::RefSll_t<next = x7> * ls(x11,x2) * x2::RefSll_t<next = x5> * x10::RefSll_t<next = x3> & null = null
         |- ls(x4,x9) * ls(x12,x7) * ls(x6,x7) * ls(x2,x5) * ls(x5,x2) * ls(x8,x10) * ls(x1,x4).

