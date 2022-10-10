
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x15::RefSll_t<next = x2> * ls(x10,x17) * x3::RefSll_t<next = x5> * ls(x11,x17) * x12::RefSll_t<next = x13> * x6::RefSll_t<next = x7> * x16::RefSll_t<next = x11> * x7::RefSll_t<next = x15> * ls(x1,x11) * x2::RefSll_t<next = x8> * x9::RefSll_t<next = x1> * x14::RefSll_t<next = x8> * ls(x17,x15) * ls(x13,x12) * x4::RefSll_t<next = x11> * x8::RefSll_t<next = x6> * x5::RefSll_t<next = x4> & null = null
         |- ls(x7,x15) * ls(x16,x11) * ls(x9,x1) * ls(x12,x13) * ls(x10,x17) * ls(x3,x5) * ls(x14,x8) * ls(x5,x4) * ls(x1,x11) * ls(x13,x12) * ls(x4,x7).

