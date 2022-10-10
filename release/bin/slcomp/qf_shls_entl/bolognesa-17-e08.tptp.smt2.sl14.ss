
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x17::RefSll_t<next = x11> * x9::RefSll_t<next = x8> * x16::RefSll_t<next = x11> * x13::RefSll_t<next = x14> * ls(x14,x3) * x6::RefSll_t<next = x10> * ls(x1,x16) * x4::RefSll_t<next = x1> * ls(x8,x4) * x2::RefSll_t<next = x9> * x10::RefSll_t<next = x5> * x5::RefSll_t<next = x11> * x3::RefSll_t<next = x14> * x11::RefSll_t<next = x17> * x12::RefSll_t<next = x4> * x15::RefSll_t<next = x3> * x7::RefSll_t<next = x11> & null = null
         |- ls(x12,x4) * ls(x15,x3) * ls(x6,x11) * ls(x7,x11) * ls(x13,x14) * ls(x14,x3) * ls(x2,x1) * ls(x1,x16) * ls(x17,x11) * ls(x16,x17) * ls(x3,x14).

