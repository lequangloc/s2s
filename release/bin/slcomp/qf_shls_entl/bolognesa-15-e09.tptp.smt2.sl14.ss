
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x2::RefSll_t<next = x3> * x11::RefSll_t<next = x3> * ls(x15,x12) * x3::RefSll_t<next = x11> * ls(x10,x12) * ls(x13,x5) * x7::RefSll_t<next = x10> * x9::RefSll_t<next = x5> * ls(x8,x13) * x4::RefSll_t<next = x5> * ls(x1,x4) * x12::RefSll_t<next = x5> * x6::RefSll_t<next = x3> * ls(x5,x12) * x14::RefSll_t<next = x11> & null = null
         |- ls(x6,x3) * ls(x15,x12) * ls(x2,x3) * ls(x9,x5) * ls(x1,x4) * ls(x8,x13) * ls(x14,x11) * ls(x3,x11) * ls(x11,x3) * ls(x7,x10) * ls(x10,x5) * ls(x4,x5) * ls(x13,x5) * ls(x5,x12).

