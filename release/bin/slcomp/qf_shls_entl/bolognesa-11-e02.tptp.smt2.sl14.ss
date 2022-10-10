
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x7::RefSll_t<next = x1> * x11::RefSll_t<next = x7> * x9::RefSll_t<next = x8> * ls(x4,x9) * x8::RefSll_t<next = x5> * x1::RefSll_t<next = x4> * ls(x10,x2) * x5::RefSll_t<next = x6> * ls(x3,x2) * x6::RefSll_t<next = x5> * x2::RefSll_t<next = x6> & null = null
         |- ls(x11,x7) * ls(x7,x9) * ls(x9,x5) * ls(x3,x2) * ls(x5,x6) * ls(x10,x5).

