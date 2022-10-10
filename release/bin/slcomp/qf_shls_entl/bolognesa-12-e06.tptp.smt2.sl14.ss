
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x9::RefSll_t<next = x2> * x12::RefSll_t<next = x5> * x6::RefSll_t<next = x9> * x7::RefSll_t<next = x5> * x11::RefSll_t<next = x3> * ls(x8,x11) * x1::RefSll_t<next = x7> * x2::RefSll_t<next = x3> * x4::RefSll_t<next = x12> * x5::RefSll_t<next = x10> * x10::RefSll_t<next = x1> * x3::RefSll_t<next = x4> & null = null
         |- ls(x7,x5) * ls(x8,x11) * ls(x6,x3) * ls(x11,x4) * ls(x4,x7).

