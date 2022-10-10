
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x10,x11) * x11::RefSll_t<next = x10> * ls(x7,x8) * x8::RefSll_t<next = x7> * ls(x4,x5) * x5::RefSll_t<next = x4> * ls(x1,x2) * x2::RefSll_t<next = x1> & null = null & null != x1 & null != x2 & null != x4 & null != x5 & null != x7 & null != x8 & null != x10 & null != x11
         |- ls(x12,x11) * x11::RefSll_t<next = x12> * ls(x9,x8) * x8::RefSll_t<next = x9> * ls(x6,x5) * x5::RefSll_t<next = x6> * ls(x3,x2) * x2::RefSll_t<next = x3>.
