
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x3::RefSll_t<next = x4> * x1::RefSll_t<next = x2> & null = null & null != x1 & null != x3
         |- x3::RefSll_t<next = x4> * x1::RefSll_t<next = x2>.

