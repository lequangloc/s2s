
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x1,x4) * x4::RefSll_t<next = x1> & null = null & null != x1 & null != x2 & null != x3 & null != x4 & x2 != x3 & x2 != x4
         |- ls(x5,x4) * x4::RefSll_t<next = x5>.

