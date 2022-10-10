
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent emp & null = null & null != x1 & x1 != x2 & x1 != x3 & x2 != x3
         |- emp.

