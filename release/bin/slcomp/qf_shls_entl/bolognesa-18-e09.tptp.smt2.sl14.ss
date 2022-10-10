
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x8,x18) * x16::RefSll_t<next = x14> * x1::RefSll_t<next = x17> * ls(x7,x9) * x4::RefSll_t<next = x3> * x10::RefSll_t<next = x5> * x13::RefSll_t<next = x2> * x18::RefSll_t<next = x1> * ls(x15,x8) * x2::RefSll_t<next = x9> * x9::RefSll_t<next = x1> * ls(x17,x4) * x3::RefSll_t<next = x8> * x6::RefSll_t<next = x17> * ls(x5,x10) * x12::RefSll_t<next = x8> * x14::RefSll_t<next = x9> * x11::RefSll_t<next = x3> & null = null
         |- ls(x7,x9) * ls(x12,x8) * ls(x6,x17) * ls(x17,x4) * ls(x15,x8) * ls(x13,x2) * ls(x11,x3) * ls(x2,x9) * ls(x10,x5) * ls(x16,x1) * ls(x5,x10) * ls(x4,x17).

