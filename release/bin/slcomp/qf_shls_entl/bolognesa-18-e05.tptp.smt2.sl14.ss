
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x4::RefSll_t<next = x12> * x10::RefSll_t<next = x6> * ls(x1,x11) * ls(x18,x8) * x13::RefSll_t<next = x9> * ls(x14,x10) * x15::RefSll_t<next = x12> * ls(x7,x16) * x3::RefSll_t<next = x11> * ls(x16,x11) * x12::RefSll_t<next = x10> * x2::RefSll_t<next = x6> * x9::RefSll_t<next = x6> * ls(x5,x9) * x6::RefSll_t<next = x1> * ls(x17,x6) * x8::RefSll_t<next = x4> * x11::RefSll_t<next = x7> & null = null
         |- ls(x16,x11) * ls(x15,x12) * ls(x17,x6) * ls(x13,x9) * ls(x14,x10) * ls(x3,x11) * ls(x5,x6) * ls(x2,x6) * ls(x18,x6) * ls(x6,x16).

