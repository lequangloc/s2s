
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x3,null) * ls(x1,null) & null = null & null != x1 & x1 != x2 & x1 != x3
         |- ls(x1,null).

