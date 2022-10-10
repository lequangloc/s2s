
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x9::RefSll_t<next = x10> * x7::RefSll_t<next = x8> * x5::RefSll_t<next = x6> * x3::RefSll_t<next = x4> * x1::RefSll_t<next = x2> & null = null & null != x1 & null != x3 & null != x5 & null != x7 & null != x9
         |- x9::RefSll_t<next = x10> * x7::RefSll_t<next = x8> * x5::RefSll_t<next = x6> * x3::RefSll_t<next = x4> * x1::RefSll_t<next = x2>.

