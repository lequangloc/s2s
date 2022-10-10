
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x13::RefSll_t<next = x3> * ls(x14,x2) * ls(x11,x12) * x4::RefSll_t<next = x12> * x10::RefSll_t<next = x15> * x2::RefSll_t<next = x1> * x8::RefSll_t<next = x2> * x6::RefSll_t<next = x8> * x12::RefSll_t<next = x6> * x3::RefSll_t<next = x4> * ls(x7,x11) * ls(x15,x2) * x5::RefSll_t<next = x7> * x1::RefSll_t<next = x6> * x9::RefSll_t<next = x11> & null = null
         |- ls(x14,x2) * ls(x13,x3) * ls(x9,x11) * ls(x10,x1) * ls(x5,x12) * ls(x3,x6) * ls(x1,x2).

