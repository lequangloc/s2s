
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x12,x4) * x10::RefSll_t<next = x11> * ls(x11,x14) * x5::RefSll_t<next = x13> * ls(x1,x11) * x3::RefSll_t<next = x2> * x6::RefSll_t<next = x2> * x4::RefSll_t<next = x14> * x2::RefSll_t<next = x6> * x13::RefSll_t<next = x5> * x14::RefSll_t<next = x4> * ls(x8,x7) * x7::RefSll_t<next = x6> * ls(x9,x12) & null = null
         |- ls(x5,x13) * ls(x9,x4) * ls(x1,x11) * ls(x13,x5) * ls(x8,x2) * ls(x10,x4) * ls(x3,x6) * ls(x4,x14).

