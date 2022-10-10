
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x6::RefSll_t<next = x15> * x5::RefSll_t<next = x14> * x9::RefSll_t<next = x3> * ls(x12,x11) * x10::RefSll_t<next = x13> * x13::RefSll_t<next = x1> * x3::RefSll_t<next = x2> * ls(x16,x7) * ls(x14,x11) * ls(x1,x11) * x11::RefSll_t<next = x15> * x8::RefSll_t<next = x1> * x15::RefSll_t<next = x5> * ls(x4,x14) * x7::RefSll_t<next = x4> * x2::RefSll_t<next = x15> & null = null
         |- ls(x6,x15) * ls(x10,x13) * ls(x9,x3) * ls(x16,x7) * ls(x3,x2) * ls(x2,x15) * ls(x8,x1) * ls(x7,x4) * ls(x12,x11) * ls(x4,x11) * ls(x13,x14).

