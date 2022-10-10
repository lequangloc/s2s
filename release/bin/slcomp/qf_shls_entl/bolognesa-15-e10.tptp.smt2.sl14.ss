
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x1::RefSll_t<next = x5> * x3::RefSll_t<next = x6> * x13::RefSll_t<next = x9> * x8::RefSll_t<next = x11> * x10::RefSll_t<next = x8> * x12::RefSll_t<next = x8> * x6::RefSll_t<next = x4> * ls(x7,x3) * x14::RefSll_t<next = x15> * x5::RefSll_t<next = x10> * ls(x15,x13) * ls(x9,x4) * ls(x11,x7) * x4::RefSll_t<next = x13> * x2::RefSll_t<next = x6> & null = null
         |- ls(x14,x15) * ls(x1,x5) * ls(x15,x13) * ls(x2,x6) * ls(x5,x8) * ls(x12,x4) * ls(x4,x13) * ls(x13,x4).

