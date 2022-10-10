
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent emp & null = null & null != x1 & null != x3 & null != x5 & null != x7 & null != x9 & null != x11 & null != x13 & null != x15 & null != x17
         |- emp.

