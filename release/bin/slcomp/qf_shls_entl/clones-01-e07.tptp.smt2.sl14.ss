
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x1,x2) * x2::RefSll_t<next = x1> & null = null & null != x1 & null != x2
         |- ls(x3,x2) * x2::RefSll_t<next = x3>.

