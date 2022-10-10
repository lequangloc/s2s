
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x2::RefSll_t<next = x6> * x4::RefSll_t<next = x1> * x11::RefSll_t<next = x8> * ls(x1,x3) * x13::RefSll_t<next = x6> * x8::RefSll_t<next = x6> * x3::RefSll_t<next = x7> * x7::RefSll_t<next = x3> * x6::RefSll_t<next = x2> * ls(x12,x7) * ls(x10,x11) * x9::RefSll_t<next = x2> * ls(x5,x11) & null = null
         |- ls(x4,x1) * ls(x9,x6) * ls(x5,x11) * ls(x12,x3) * ls(x13,x6) * ls(x10,x11) * ls(x1,x7) * ls(x11,x2).

