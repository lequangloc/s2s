
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x7::RefSll_t<next = x11> * x5::RefSll_t<next = x10> * x10::RefSll_t<next = x6> * x3::RefSll_t<next = x7> * x1::RefSll_t<next = x8> * ls(x4,x9) * x11::RefSll_t<next = x1> * x6::RefSll_t<next = x9> * x9::RefSll_t<next = x2> * x2::RefSll_t<next = x6> * x8::RefSll_t<next = x11> & null = null
         |- ls(x5,x10) * ls(x2,x6) * ls(x4,x9) * ls(x3,x7) * ls(x7,x1) * ls(x1,x11) * ls(x10,x2).

