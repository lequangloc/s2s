
data RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent[valid] x3::RefSll_t<next = x10> * ls(x5,x10) * ls(x11,x2) * x10::RefSll_t<next = x2> * x2::RefSll_t<next = x1> * x7::RefSll_t<next = x4> * x1::RefSll_t<next = x9> * x9::RefSll_t<next = x1> * ls(x8,x10) * x6::RefSll_t<next = x5> * x4::RefSll_t<next = x7> & null = null
         |- ls(x9,x1) * ls(x6,x5) * ls(x8,x10) * ls(x3,x10) * ls(x7,x4) * ls(x5,x10) * ls(x10,x2) * ls(x4,x7) * ls(x11,x9).

