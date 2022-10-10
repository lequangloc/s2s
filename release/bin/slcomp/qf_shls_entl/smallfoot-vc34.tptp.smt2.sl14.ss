
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x2,x3) * ls(x4,null) * x3::RefSll_t<next = x4> & null = null & null != x1 & null != x2 & null != x3 & x1 != x2 & x1 != x4 & x1 != x3 & x2 != x4 & x3 != x4
         |- ls(x4,null) * x3::RefSll_t<next = x4> * ls(x2,x3).

