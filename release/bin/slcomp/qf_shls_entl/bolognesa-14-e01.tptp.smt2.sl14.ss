
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x3::RefSll_t<next = x6> * x2::RefSll_t<next = x12> * ls(x1,x7) * x14::RefSll_t<next = x11> * x8::RefSll_t<next = x11> * x12::RefSll_t<next = x1> * x13::RefSll_t<next = x4> * x10::RefSll_t<next = x5> * x5::RefSll_t<next = x2> * x4::RefSll_t<next = x14> * ls(x9,x4) * ls(x6,x8) * x11::RefSll_t<next = x13> * ls(x7,x14) & null = null
         |- ls(x9,x4) * ls(x10,x5) * ls(x3,x11) * ls(x4,x14) * ls(x5,x4).

