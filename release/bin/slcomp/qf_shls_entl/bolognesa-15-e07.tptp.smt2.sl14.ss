
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x1::RefSll_t<next = x5> * x11::RefSll_t<next = x2> * x10::RefSll_t<next = x4> * x12::RefSll_t<next = x13> * x6::RefSll_t<next = x2> * x14::RefSll_t<next = x10> * ls(x5,x11) * x9::RefSll_t<next = x3> * ls(x8,x4) * ls(x13,x4) * x2::RefSll_t<next = x7> * x3::RefSll_t<next = x1> * ls(x15,x13) * x4::RefSll_t<next = x3> * x7::RefSll_t<next = x10> & null = null
         |- ls(x6,x2) * ls(x12,x13) * ls(x9,x3) * ls(x15,x4) * ls(x7,x10) * ls(x8,x4) * ls(x14,x10) * ls(x10,x7).

