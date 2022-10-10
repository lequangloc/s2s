
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x3::RefSll_t<next = x15> * x13::RefSll_t<next = x14> * x2::RefSll_t<next = x7> * x15::RefSll_t<next = x9> * ls(x16,x5) * x11::RefSll_t<next = x6> * ls(x9,x5) * x1::RefSll_t<next = x3> * ls(x12,x10) * ls(x4,x1) * x5::RefSll_t<next = x1> * x10::RefSll_t<next = x8> * x7::RefSll_t<next = x10> * x14::RefSll_t<next = x16> * ls(x6,x3) * x8::RefSll_t<next = x2> & null = null
         |- ls(x7,x10) * ls(x12,x10) * ls(x4,x1) * ls(x13,x5) * ls(x11,x15) * ls(x15,x3) * ls(x10,x7).

