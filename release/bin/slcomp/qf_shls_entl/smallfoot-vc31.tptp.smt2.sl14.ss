
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x1::RefSll_t<next = x6> * ls(x2,x1) * x6::RefSll_t<next = x2> & null = null & null != x1 & null != x2 & null != x3 & null != x4 & null != x5 & null != x6 & x1 != x6 & x2 != x6 & x3 != x4 & x3 != x5
         |- ls(x7,x6) * x6::RefSll_t<next = x7> & x6 != x7.

