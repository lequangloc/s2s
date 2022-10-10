
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x1::RefSll_t<next = x11> * x3::RefSll_t<next = x1> * x6::RefSll_t<next = x2> * x9::RefSll_t<next = x6> * x4::RefSll_t<next = x1> * x8::RefSll_t<next = x3> * x5::RefSll_t<next = x11> * ls(x7,x9) * x11::RefSll_t<next = x3> * x2::RefSll_t<next = x11> * ls(x10,x11) & null = null
         |- ls(x8,x3) * ls(x7,x9) * ls(x3,x1) * ls(x4,x1) * ls(x9,x11) * ls(x10,x11) * ls(x5,x11) * ls(x1,x3).

