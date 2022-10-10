
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x4::RefSll_t<next = x8> * x7::RefSll_t<next = x5> * x1::RefSll_t<next = x10> * x3::RefSll_t<next = x7> * ls(x5,x12) * ls(x10,x13) * ls(x13,x9) * x8::RefSll_t<next = x11> * ls(x12,x4) * x6::RefSll_t<next = x12> * x2::RefSll_t<next = x4> * ls(x9,x11) * x11::RefSll_t<next = x6> & null = null
         |- ls(x1,x13) * ls(x2,x4) * ls(x13,x11) * ls(x11,x6) * ls(x3,x12) * ls(x6,x11).

