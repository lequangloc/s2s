
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x11,x14) * x4::RefSll_t<next = x9> * x2::RefSll_t<next = x5> * x3::RefSll_t<next = x12> * ls(x14,x11) * ls(x10,x13) * x6::RefSll_t<next = x2> * x15::RefSll_t<next = x6> * x7::RefSll_t<next = x5> * x1::RefSll_t<next = x13> * x5::RefSll_t<next = x1> * x13::RefSll_t<next = x12> * x8::RefSll_t<next = x12> * ls(x12,x5) * ls(x9,x8) & null = null
         |- ls(x15,x6) * ls(x10,x13) * ls(x6,x2) * ls(x3,x12) * ls(x4,x9) * ls(x2,x5) * ls(x9,x8) * ls(x13,x12) * ls(x7,x5) * ls(x8,x13) * ls(x14,x11) * ls(x11,x14).

