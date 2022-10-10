
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x12,x2) * x3::RefSll_t<next = x6> * x1::RefSll_t<next = x7> * x4::RefSll_t<next = x13> * ls(x7,x3) * x11::RefSll_t<next = x4> * ls(x6,x1) * x8::RefSll_t<next = x10> * x10::RefSll_t<next = x6> * x2::RefSll_t<next = x3> * x5::RefSll_t<next = x6> * ls(x9,x8) * ls(x13,x4) & null = null
         |- ls(x11,x4) * ls(x5,x6) * ls(x9,x6) * ls(x4,x13) * ls(x13,x4) * ls(x12,x6) * ls(x6,x3).

