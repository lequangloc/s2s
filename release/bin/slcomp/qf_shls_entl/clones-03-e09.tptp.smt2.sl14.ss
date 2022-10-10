
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x11,x9) * x9::RefSll_t<next = x11> * ls(x7,x5) * x5::RefSll_t<next = x7> * ls(x3,x1) * x1::RefSll_t<next = x3> & null = null & null != x1 & null != x2 & null != x3 & x1 != x2 & x2 != x3 & null != x5 & null != x6 & null != x7 & x5 != x6 & x6 != x7 & null != x9 & null != x10 & null != x11 & x9 != x10 & x10 != x11
         |- ls(x12,x9) * x9::RefSll_t<next = x12> * ls(x8,x5) * x5::RefSll_t<next = x8> * ls(x4,x1) * x1::RefSll_t<next = x4>.

