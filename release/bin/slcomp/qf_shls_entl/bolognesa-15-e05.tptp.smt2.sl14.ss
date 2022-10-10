
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x11,x15) * x4::RefSll_t<next = x5> * x5::RefSll_t<next = x11> * ls(x1,x12) * ls(x12,x13) * ls(x7,x6) * x3::RefSll_t<next = x1> * ls(x9,x11) * x2::RefSll_t<next = x8> * x10::RefSll_t<next = x5> * x15::RefSll_t<next = x5> * x14::RefSll_t<next = x6> * x13::RefSll_t<next = x4> * x8::RefSll_t<next = x11> * x6::RefSll_t<next = x8> & null = null
         |- ls(x15,x5) * ls(x9,x11) * ls(x10,x5) * ls(x3,x1) * ls(x7,x6) * ls(x2,x8) * ls(x1,x4) * ls(x4,x5) * ls(x14,x11) * ls(x5,x15).

