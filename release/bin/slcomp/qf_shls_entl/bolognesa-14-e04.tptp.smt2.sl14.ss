
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x11,x8) * x10::RefSll_t<next = x12> * x7::RefSll_t<next = x14> * x3::RefSll_t<next = x12> * x5::RefSll_t<next = x9> * x8::RefSll_t<next = x12> * x13::RefSll_t<next = x11> * x12::RefSll_t<next = x9> * x14::RefSll_t<next = x5> * x6::RefSll_t<next = x3> * x4::RefSll_t<next = x11> * ls(x1,x7) * x2::RefSll_t<next = x1> * x9::RefSll_t<next = x13> & null = null
         |- ls(x4,x11) * ls(x2,x7) * ls(x8,x12) * ls(x10,x12) * ls(x6,x12) * ls(x7,x5) * ls(x5,x9) * ls(x12,x8).

