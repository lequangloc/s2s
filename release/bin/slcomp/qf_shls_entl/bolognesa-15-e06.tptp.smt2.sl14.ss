
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x6,x1) * ls(x11,x6) * ls(x15,x6) * ls(x12,x1) * x5::RefSll_t<next = x8> * x7::RefSll_t<next = x10> * x8::RefSll_t<next = x15> * x2::RefSll_t<next = x14> * ls(x9,x5) * ls(x4,x3) * x3::RefSll_t<next = x10> * x10::RefSll_t<next = x3> * ls(x13,x7) * ls(x14,x7) * x1::RefSll_t<next = x7> & null = null
         |- ls(x12,x1) * ls(x9,x5) * ls(x11,x6) * ls(x13,x7) * ls(x4,x3) * ls(x3,x10) * ls(x5,x8) * ls(x8,x15) * ls(x15,x7) * ls(x2,x3).

