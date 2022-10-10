
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x2::RefSll_t<next = x3> * x9::RefSll_t<next = x15> * x13::RefSll_t<next = x16> * x6::RefSll_t<next = x12> * ls(x10,x11) * x4::RefSll_t<next = x11> * x11::RefSll_t<next = x7> * ls(x5,x6) * x8::RefSll_t<next = x3> * x16::RefSll_t<next = x8> * ls(x1,x14) * x14::RefSll_t<next = x1> * x3::RefSll_t<next = x7> * x15::RefSll_t<next = x12> * ls(x7,x16) * x12::RefSll_t<next = x5> & null = null
         |- ls(x6,x12) * ls(x1,x14) * ls(x13,x16) * ls(x10,x11) * ls(x9,x15) * ls(x14,x1) * ls(x2,x7) * ls(x4,x3) * ls(x15,x6).

