
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x2,null) * ls(x1,null) & null = null & null != x1 & x1 != x2
         |- ls(x1,null) * ls(x2,null).

