
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x5::RefSll_t<next = x6> * x12::RefSll_t<next = x4> * x8::RefSll_t<next = x6> * ls(x1,x8) * x11::RefSll_t<next = x5> * ls(x4,x3) * x2::RefSll_t<next = x4> * x9::RefSll_t<next = x6> * x3::RefSll_t<next = x7> * ls(x6,x8) * x7::RefSll_t<next = x10> * ls(x10,x3) & null = null
         |- ls(x9,x6) * ls(x2,x4) * ls(x12,x7) * ls(x11,x8) * ls(x1,x6) * ls(x7,x3).

