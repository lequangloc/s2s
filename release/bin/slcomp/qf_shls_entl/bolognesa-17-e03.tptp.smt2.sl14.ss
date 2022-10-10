
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x14::RefSll_t<next = x12> * ls(x2,x15) * ls(x17,x13) * x11::RefSll_t<next = x4> * x5::RefSll_t<next = x17> * x3::RefSll_t<next = x11> * x8::RefSll_t<next = x6> * ls(x6,x5) * ls(x10,x4) * ls(x16,x2) * ls(x7,x14) * x1::RefSll_t<next = x17> * x12::RefSll_t<next = x15> * x4::RefSll_t<next = x14> * x13::RefSll_t<next = x8> * x9::RefSll_t<next = x5> * x15::RefSll_t<next = x13> & null = null
         |- ls(x1,x17) * ls(x9,x5) * ls(x7,x14) * ls(x17,x13) * ls(x16,x15) * ls(x3,x4) * ls(x10,x17).

