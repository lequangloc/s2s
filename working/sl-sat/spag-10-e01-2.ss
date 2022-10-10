
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checksat[unsat]  ls(x2,x10)  * ls(x9,x1) * ls(x7,x6)* ls(x2,x1) * ls(x3,x10) * ls(x6,x9) * ls(x5,x7) * ls(x2,x5) & null = null & x1 != x6 & x1 != x7 & x1 != x10 & x4 != x8 & x4 != x7 & x4 != x9 & x3 != x8 & x7 != x10 & x2 != x6 & x2 != x3 & x2 != x7.

