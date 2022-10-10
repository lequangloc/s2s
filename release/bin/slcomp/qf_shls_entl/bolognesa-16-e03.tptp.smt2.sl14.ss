
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x3::RefSll_t<next = x5> * x6::RefSll_t<next = x2> * ls(x8,x2) * x14::RefSll_t<next = x15> * x13::RefSll_t<next = x11> * x15::RefSll_t<next = x4> * ls(x2,x9) * x10::RefSll_t<next = x5> * x11::RefSll_t<next = x3> * x9::RefSll_t<next = x16> * ls(x5,x13) * x4::RefSll_t<next = x9> * x1::RefSll_t<next = x3> * x12::RefSll_t<next = x13> * ls(x16,x9) * x7::RefSll_t<next = x1> & null = null
         |- ls(x6,x2) * ls(x12,x13) * ls(x8,x2) * ls(x11,x3) * ls(x2,x9) * ls(x7,x1) * ls(x16,x9) * ls(x10,x5) * ls(x14,x16) * ls(x1,x3) * ls(x3,x11).

