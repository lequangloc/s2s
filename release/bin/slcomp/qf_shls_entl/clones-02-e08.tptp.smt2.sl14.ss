
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x6,x5) * x7::RefSll_t<next = x6> * x5::RefSll_t<next = x7> * ls(x2,x1) * x3::RefSll_t<next = x2> * x1::RefSll_t<next = x3> & null = null & null != x1 & null != x2 & null != x3 & x1 != x3 & x2 != x3 & null != x5 & null != x6 & null != x7 & x5 != x7 & x6 != x7
         |- x8::RefSll_t<next = x7> * ls(x6,x8) * x7::RefSll_t<next = x6> * x4::RefSll_t<next = x3> * ls(x2,x4) * x3::RefSll_t<next = x2>.

