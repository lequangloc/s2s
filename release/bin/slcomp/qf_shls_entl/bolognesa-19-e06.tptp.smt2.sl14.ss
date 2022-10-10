
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x15::RefSll_t<next = x5> * x2::RefSll_t<next = x17> * ls(x13,x19) * x12::RefSll_t<next = x7> * ls(x6,x14) * x3::RefSll_t<next = x15> * x7::RefSll_t<next = x14> * x14::RefSll_t<next = x16> * x4::RefSll_t<next = x7> * ls(x16,x12) * ls(x17,x3) * x10::RefSll_t<next = x3> * x11::RefSll_t<next = x18> * x18::RefSll_t<next = x6> * x19::RefSll_t<next = x2> * x9::RefSll_t<next = x4> * x1::RefSll_t<next = x5> * ls(x8,x4) * x5::RefSll_t<next = x15> & null = null
         |- ls(x12,x7) * ls(x1,x5) * ls(x9,x4) * ls(x11,x18) * ls(x18,x14) * ls(x13,x19) * ls(x8,x12) * ls(x5,x15) * ls(x19,x3) * ls(x10,x5).

