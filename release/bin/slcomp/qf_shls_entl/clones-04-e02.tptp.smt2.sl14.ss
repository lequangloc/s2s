
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent emp & null = null & null != x1 & null != x2 & x1 != x2 & null != x3 & null != x4 & x3 != x4 & null != x5 & null != x6 & x5 != x6 & null != x7 & null != x8 & x7 != x8
         |- emp.

