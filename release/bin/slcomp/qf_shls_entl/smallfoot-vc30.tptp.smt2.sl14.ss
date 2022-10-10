
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x1,x7) * x7::RefSll_t<next = x1> & null = null & null != x1 & null != x2 & null != x3 & null != x4 & null != x5 & null != x6 & null != x7 & x2 != x7 & x3 != x7 & x4 != x5 & x4 != x6
         |- ls(x8,x7) * x7::RefSll_t<next = x8>.

