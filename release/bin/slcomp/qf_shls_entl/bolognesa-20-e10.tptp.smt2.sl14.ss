
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x19::RefSll_t<next = x10> * x9::RefSll_t<next = x1> * x6::RefSll_t<next = x11> * x12::RefSll_t<next = x2> * x5::RefSll_t<next = x6> * x1::RefSll_t<next = x12> * x13::RefSll_t<next = x14> * x18::RefSll_t<next = x12> * x14::RefSll_t<next = x2> * ls(x7,x5) * x15::RefSll_t<next = x13> * x10::RefSll_t<next = x7> * ls(x3,x18) * ls(x8,x14) * x16::RefSll_t<next = x7> * x11::RefSll_t<next = x5> * x4::RefSll_t<next = x2> * x2::RefSll_t<next = x15> * ls(x17,x19) * x20::RefSll_t<next = x11> & null = null
         |- ls(x8,x14) * ls(x14,x2) * ls(x16,x7) * ls(x4,x2) * ls(x20,x11) * ls(x17,x5) * ls(x5,x6) * ls(x6,x5) * ls(x3,x12) * ls(x9,x14).

