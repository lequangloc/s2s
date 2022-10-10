
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x3,null) * x2::RefSll_t<next = x3> & null = null & null != x1 & null != x2 & x2 != x3 & x1 != x4 & x2 != x4 & x1 != x2
         |- ls(x2,null).

